#include <hardware/gps.h>

#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/epoll.h>
#include <termios.h>
#include <fcntl.h>
#include <unistd.h>
#include <math.h>
#include <time.h>
#include <pthread.h>
#define  LOG_TAG  "mingxin_gps"
#include <cutils/log.h>

#define LOGD(...) __android_log_print(ANDROID_LOG_DEBUG, LOG_TAG, __VA_ARGS__)
#define LOGE(...) __android_log_print(ANDROID_LOG_ERROR, LOG_TAG, __VA_ARGS__)

// jni callback function pointer
static gps_location_callback location_cb     = NULL;
static gps_status_callback status_cb         = NULL;
static gps_sv_status_callback svstatus_cb    = NULL;
static gps_nmea_callback nmea_cb             = NULL;
static gps_set_capabilities setcap_cb        = NULL;
static gps_acquire_wakelock acquire_lock_cb  = NULL;
static gps_release_wakelock rel_lock_cb      = NULL;
static gps_create_thread thread_cb           = NULL;

static int gss_fd   = -1;
static int init     = 0;
static char *buff   = NULL;
pthread_t  thread;

// Function declarations for sLocEngInterface
static int  loc_init(GpsCallbacks* callbacks);
static int  loc_start();
static int  loc_stop();
static void loc_cleanup();
static int  loc_inject_time(GpsUtcTime time, int64_t timeReference, int uncertainty);
static int  loc_inject_location(double latitude, double longitude, float accuracy);
static void loc_delete_aiding_data(GpsAidingData f);
static int  loc_set_position_mode(GpsPositionMode mode, GpsPositionRecurrence recurrence,
                                  uint32_t min_interval, uint32_t preferred_accuracy, uint32_t preferred_time);
static const void* loc_get_extension(const char* name);
static void gps_state_thread( void*  arg );


// Defines the GpsInterface in gps.h
static const GpsInterface sLocEngInterface =
{
    sizeof(GpsInterface),
    loc_init,
    loc_start,
    loc_stop,
    loc_cleanup,
    loc_inject_time,
    loc_inject_location,
    loc_delete_aiding_data,
    loc_set_position_mode,
    loc_get_extension
};

typedef struct
{
    const char*  p;
    const char*  end;
} Token;

#define  BUFF_LEN         512
#define  MAX_NMEA_TOKENS  25
#define  GPS_DEBUG        1
#define  GPS_LOCATION_ALL  (GPS_LOCATION_HAS_ACCURACY|GPS_LOCATION_HAS_ALTITUDE|GPS_LOCATION_HAS_BEARING|GPS_LOCATION_HAS_LAT_LONG|GPS_LOCATION_HAS_SPEED)

#if GPS_DEBUG
#define  D(...)   ALOGD(__VA_ARGS__)
#else
#define  D(...)   ((void)0)
#endif

typedef struct
{
    int     count;
    Token   tokens[ MAX_NMEA_TOKENS ];
} NmeaTokenizer;

static int nmea_tokenizer_init( NmeaTokenizer*  t, const char*  p, const char*  end )
{
    int    count = 0;
    char*  q;

    // the initial '$' is optional
    if (p < end && p[0] == '$')
        p += 1;

    // remove trailing newline
    if (end > p && end[-1] == '\n') {
        end -= 1;
        if (end > p && end[-1] == '\r')
            end -= 1;
    }

    // get rid of checksum at the end of the sentecne
    if (end >= p+3 && end[-3] == '*') {
        end -= 3;
    }

    while (p < end) {
        const char*  q = p;

        q = memchr(p, ',', end-p);
        if (q == NULL)
            q = end;

        if (q >= p) {    //bug = --> >=
            if (count < MAX_NMEA_TOKENS) {
                t->tokens[count].p   = p;
                t->tokens[count].end = q;
                count += 1;
            }
        }
        if (q < end)
            q += 1;

        p = q;
    }

    t->count = count;
    return count;
}

static Token nmea_tokenizer_get( NmeaTokenizer*  t, int  index )
{
    Token  tok;
    static const char*  dummy = "";

    if (index < 0 || index >= t->count) {
        tok.p = tok.end = dummy;
    } else
        tok = t->tokens[index];

    return tok;
}


static int str2int( const char*  p, const char*  end )
{
    int   result = 0;
    int   len    = end - p;

    for ( ; len > 0; len--, p++ )
    {
        int  c;

        if (p >= end)
            goto Fail;

        c = *p - '0';
        if ((unsigned)c >= 10)
            goto Fail;

        result = result*10 + c;
    }
    return  result;

Fail:
    return -1;
}

static double str2float( const char*  p, const char*  end )
{
    int   result = 0;
    int   len    = end - p;
    char  temp[16];

    if (len >= (int)sizeof(temp))
        return 0.;

    memcpy( temp, p, len );
    temp[len] = 0;
    return strtod( temp, NULL );
}

#define  NMEA_MAX_SIZE  83

typedef struct
{
    int     pos;
    int     overflow;
    int     utc_year;
    int     utc_mon;
    int     utc_day;
    int     utc_diff;
    GpsLocation  fix;
    int     sv_status_changed;
	GpsSvStatus sv_status;
    
    char    in[ NMEA_MAX_SIZE+1 ];
} NmeaReader;


static void nmea_reader_update_utc_diff( NmeaReader*  r )
{
    time_t         now = time(NULL);
    struct tm      tm_local;
    struct tm      tm_utc;
    long           time_local, time_utc;

    gmtime_r( &now, &tm_utc );
    localtime_r( &now, &tm_local );

    time_local = tm_local.tm_sec +
                 60*(tm_local.tm_min +
                 60*(tm_local.tm_hour +
                 24*(tm_local.tm_yday +
                 365*tm_local.tm_year)));

    time_utc = tm_utc.tm_sec +
               60*(tm_utc.tm_min +
               60*(tm_utc.tm_hour +
               24*(tm_utc.tm_yday +
               365*tm_utc.tm_year)));

    r->utc_diff = time_local - time_utc;  //bug
}


static void nmea_reader_init( NmeaReader*  r )
{
    memset( r, 0, sizeof(*r) );

    r->pos      = 0;
    r->overflow = 0;
    r->utc_year = -1;
    r->utc_mon  = -1;
    r->utc_day  = -1;

    r->fix.size = sizeof(r->fix);

    nmea_reader_update_utc_diff( r );

	r->sv_status.size = sizeof(r->sv_status);
}


static int nmea_reader_update_time( NmeaReader*  r, Token  tok )
{
    int        hour, minute;
    double     seconds;
    struct tm  tm;
    time_t     fix_time;

    if (tok.p + 6 > tok.end)
        return -1;

    if (r->utc_year < 0) {
        // no date yet, get current one
        time_t  now = time(NULL);
        gmtime_r( &now, &tm );
        r->utc_year = tm.tm_year + 1900;
        r->utc_mon  = tm.tm_mon + 1;
        r->utc_day  = tm.tm_mday;
    }

    hour    = str2int(tok.p,   tok.p+2);
    minute  = str2int(tok.p+2, tok.p+4);
    seconds = str2float(tok.p+4, tok.end);

    tm.tm_hour  = hour;
    tm.tm_min   = minute;
    tm.tm_sec   = (int) seconds;
    tm.tm_year  = r->utc_year - 1900;
    tm.tm_mon   = r->utc_mon - 1;
    tm.tm_mday  = r->utc_day;
    tm.tm_isdst = -1;

    fix_time = mktime( &tm ) + r->utc_diff;
    r->fix.timestamp = (long long)fix_time * 1000;
    return 0;
}

static int nmea_reader_update_date( NmeaReader*  r, Token  date, Token  time )
{
    Token  tok = date;
    int    day, mon, year;

    if (tok.p + 6 != tok.end) {
        D("date not properly formatted: '%.*s'\n", tok.end-tok.p, tok.p);
        return -1;
    }
    day  = str2int(tok.p, tok.p+2);
    mon  = str2int(tok.p+2, tok.p+4);
    year = str2int(tok.p+4, tok.p+6) + 2000;

    if ((day|mon|year) < 0) {
        D("date not properly formatted: '%.*s'\n", tok.end-tok.p, tok.p);
        return -1;
    }

    r->utc_year  = year;
    r->utc_mon   = mon;
    r->utc_day   = day;

    return nmea_reader_update_time( r, time );
}


static double convert_from_hhmm( Token  tok )
{
    double  val     = str2float(tok.p, tok.end);
    int     degrees = (int)(floor(val) / 100);
    double  minutes = val - degrees*100.;
    double  dcoord  = degrees + minutes / 60.0;
    return dcoord;
}


static int nmea_reader_update_latlong( NmeaReader*  r,
                            Token        latitude,
                            char         latitudeHemi,
                            Token        longitude,
                            char         longitudeHemi )
{
    double   lat, lon;
    Token    tok;

    tok = latitude;
    if (tok.p + 6 > tok.end) {
        D("latitude is too short: '%.*s'\n", tok.end-tok.p, tok.p);
        return -1;
    }
    lat = convert_from_hhmm(tok);
    if (latitudeHemi == 'S')
        lat = -lat;

    tok = longitude;
    if (tok.p + 6 > tok.end) {
        D("longitude is too short: '%.*s'\n", tok.end-tok.p, tok.p);
        return -1;
    }
    lon = convert_from_hhmm(tok);
    if (longitudeHemi == 'W')
        lon = -lon;

    r->fix.flags    |= GPS_LOCATION_HAS_LAT_LONG;
    r->fix.latitude  = lat;
    r->fix.longitude = lon;

    return 0;
}


static int nmea_reader_update_altitude( NmeaReader*  r,
                             Token        altitude,
                             Token        units )
{
    //double  alt;
    Token   tok = altitude;

    if (tok.p >= tok.end)
        return -1;

    r->fix.flags   |= GPS_LOCATION_HAS_ALTITUDE;
    r->fix.altitude = str2float(tok.p, tok.end);
    return 0;
}


static int nmea_reader_update_bearing( NmeaReader*  r,
                            Token        bearing )
{
    //double  alt;
    Token   tok = bearing;

    if (tok.p >= tok.end)
        return -1;

    r->fix.flags   |= GPS_LOCATION_HAS_BEARING;
    r->fix.bearing  = str2float(tok.p, tok.end);
    return 0;
}

static int nmea_reader_update_accuracy(NmeaReader*  r,
                            Token accuracy)
{
    Token   tok = accuracy;

    if (tok.p >= tok.end)
        return -1;

    r->fix.flags   |= GPS_LOCATION_HAS_ACCURACY;
    r->fix.accuracy = str2float(tok.p, tok.end);
    return 0;	
}

static int nmea_reader_update_speed( NmeaReader*  r,
                          Token        speed )
{
    double  alt;
    Token   tok = speed;

    if (tok.p >= tok.end)
        return -1;

    r->fix.flags   |= GPS_LOCATION_HAS_SPEED;
    r->fix.speed    = str2float(tok.p, tok.end);
    return 0;
}


static void nmea_reader_parse( NmeaReader*  r )
{
   /* we received a complete sentence, now parse it to generate
    * a new GPS fix...
    */
    NmeaTokenizer  tzer[1];
    Token          tok;

    //D("Received: '%.*s'", r->pos, r->in);
    if (r->pos < 9) {
        //D("Too short. discarded.\n");
        return;
    }

    nmea_tokenizer_init(tzer, r->in, r->in + r->pos);
    #if 0
    {
        int  n;
        D("Found %d tokens:", tzer->count);
        for (n = 0; n < tzer->count; n++) {
            Token  tok = nmea_tokenizer_get(tzer,n);
            D("%2d: '%.*s'", n, tok.end-tok.p, tok.p);
        }
    }
    #endif

    tok = nmea_tokenizer_get(tzer, 0);
    if (tok.p + 5 > tok.end) {
        D("sentence id '%.*s' too short, ignored.\n", tok.end-tok.p, tok.p);
        return;
    }

    // ignore first two characters.
    tok.p += 2;
    if ( !memcmp(tok.p, "GGA", 3) ) {
        // GPS fix
        Token  tok_time          = nmea_tokenizer_get(tzer,1);
        Token  tok_latitude      = nmea_tokenizer_get(tzer,2);
        Token  tok_latitudeHemi  = nmea_tokenizer_get(tzer,3);
        Token  tok_longitude     = nmea_tokenizer_get(tzer,4);
        Token  tok_longitudeHemi = nmea_tokenizer_get(tzer,5);
        Token  tok_fixindicator  = nmea_tokenizer_get(tzer,6);
        Token  tok_satelliteNum  = nmea_tokenizer_get(tzer,7);
        Token  tok_altitude      = nmea_tokenizer_get(tzer,9);
        Token  tok_altitudeUnits = nmea_tokenizer_get(tzer,10);

        if (tok_fixindicator.p[0] != '0' )
        {
            D("in GGA, satellite num=%c%c\n", tok_satelliteNum.p[0], tok_satelliteNum.p[1]);
            nmea_reader_update_time(r, tok_time);
            nmea_reader_update_latlong(r, tok_latitude,
                                      tok_latitudeHemi.p[0],
                                      tok_longitude,
                                      tok_longitudeHemi.p[0]);
            nmea_reader_update_altitude(r, tok_altitude, tok_altitudeUnits);
        }
    } 
    else if ( !memcmp(tok.p, "RMC", 3) )
    {
        Token  tok_time          = nmea_tokenizer_get(tzer,1);
        Token  tok_fixStatus     = nmea_tokenizer_get(tzer,2);
        Token  tok_latitude      = nmea_tokenizer_get(tzer,3);
        Token  tok_latitudeHemi  = nmea_tokenizer_get(tzer,4);
        Token  tok_longitude     = nmea_tokenizer_get(tzer,5);
        Token  tok_longitudeHemi = nmea_tokenizer_get(tzer,6);
        Token  tok_speed         = nmea_tokenizer_get(tzer,7);
        Token  tok_bearing       = nmea_tokenizer_get(tzer,8);
        Token  tok_date          = nmea_tokenizer_get(tzer,9);

        D("in RMC, fixStatus=%c\n", tok_fixStatus.p[0]);
        if (tok_fixStatus.p[0] == 'A')
        {
            nmea_reader_update_date( r, tok_date, tok_time );

            nmea_reader_update_latlong( r, tok_latitude,
                                           tok_latitudeHemi.p[0],
                                           tok_longitude,
                                           tok_longitudeHemi.p[0] );

            nmea_reader_update_bearing( r, tok_bearing );
            nmea_reader_update_speed  ( r, tok_speed );
        }
    }

    else if ( !memcmp(tok.p, "GSV", 3) ) { 
        Token tok_noSatellites = nmea_tokenizer_get(tzer, 3); 
        int noSatellites = str2int(tok_noSatellites.p, tok_noSatellites.end); 
        D("GSV: Satellite inview=%d\n", noSatellites);     

        if (noSatellites > 0 && r->sv_status_changed != 0)
        { 
            Token tok_noSentences = nmea_tokenizer_get(tzer, 1); 
            Token tok_sentence    = nmea_tokenizer_get(tzer, 2); 
         
            int sentence = str2int(tok_sentence.p, tok_sentence.end); 
            int totalSentences = str2int(tok_noSentences.p, tok_noSentences.end); 
            //D("gsv_index=%d, gsv_total=%d\n",sentence,totalSentences);   
            if (sentence == 1) { 
            //  r->sv_status_changed = 0; 
                r->sv_status.num_svs = 0; 
                r->sv_status.ephemeris_mask=0ul; 
                r->sv_status.almanac_mask=0ul; 
            } 
             
            int curr = r->sv_status.num_svs; 
            int i = 0; 
            while (i < 4 && r->sv_status.num_svs < noSatellites) { 
                Token      tok_prn = nmea_tokenizer_get(tzer, i * 4 + 4); 
                Token      tok_elevation = nmea_tokenizer_get(tzer, i * 4 + 5); 
                Token      tok_azimuth = nmea_tokenizer_get(tzer, i * 4 + 6); 
                Token      tok_snr = nmea_tokenizer_get(tzer, i * 4 + 7); 
             
                r->sv_status.sv_list[curr].prn = str2int(tok_prn.p, tok_prn.end); 
                r->sv_status.sv_list[curr].elevation = str2float(tok_elevation.p, tok_elevation.end); 
                r->sv_status.sv_list[curr].azimuth = str2float(tok_azimuth.p, tok_azimuth.end); 
                r->sv_status.sv_list[curr].snr = str2float(tok_snr.p, tok_snr.end); 
                r->sv_status.ephemeris_mask|=(1ul << (r->sv_status.sv_list[curr].prn-1)); 
                r->sv_status.almanac_mask|=(1ul << (r->sv_status.sv_list[curr].prn-1));          
                r->sv_status.num_svs += 1; 
                //D("GSV: curr=%d:prn=%d:snr=%f\n",curr,r->sv_status.sv_list[curr].prn,r->sv_status.sv_list[curr].snr); 
                curr += 1; 
                i += 1; 
            } 
             
            if (sentence == totalSentences) { 
                if (svstatus_cb) { 
                    #if GPS_DEBUG 
                    int nums=r->sv_status.num_svs; 
                    D("GSV: num_svs=%d,emask=%x,amask=%x,inusemask=%x\n",r->sv_status.num_svs,r->sv_status.ephemeris_mask,r->sv_status.almanac_mask,r->sv_status.used_in_fix_mask); 
                    while(nums) 
                    { 
                        nums--; 
                        D("prn=%d:snr=%f\n",r->sv_status.sv_list[nums].prn,r->sv_status.sv_list[nums].snr); 
                    }
                    #endif 
                    svstatus_cb( &(r->sv_status) );
                    r->sv_status_changed = 0;
                }
                else { 
                    LOGE("sv_status_cb no callback!"); 
                }
            } 
        }           
    }
	
    else if ( !memcmp(tok.p, "GSA", 3) ) { 
        Token tok_fixStatus = nmea_tokenizer_get(tzer, 2); 
        int i; 
         
        if (tok_fixStatus.p[0] != '\0' && tok_fixStatus.p[0] != '1') 
        {
            Token tok_accuracy = nmea_tokenizer_get(tzer, 15);//position dilution of precision dop 
            nmea_reader_update_accuracy(r, tok_accuracy); 
            
            r->sv_status.used_in_fix_mask = 0ul; 
            for (i = 3; i <= 14; ++i) { 
                Token tok_prn = nmea_tokenizer_get(tzer, i); 
                int prn = str2int(tok_prn.p, tok_prn.end); 
                //D("GSA: prn=%d,",prn); 
                if (prn > 0) { 
                    r->sv_status.used_in_fix_mask |= (1ul << ( prn-1)); 
                    r->sv_status_changed = 1; 
                } 
            }
            D("GSA: fix mask is %x", r->sv_status.used_in_fix_mask); 
        } 
    }

    else if ( !memcmp(tok.p, "GLL", 3) ) {
        // todo
    }
    else if ( !memcmp(tok.p, "VTG", 3) ) {
        // todo
    }
    else {
        tok.p -= 2;
        D("unknown sentence '%.*s\n", tok.end-tok.p, tok.p);
    }

    if ((r->fix.flags & GPS_LOCATION_HAS_LAT_LONG) && (r->fix.flags & GPS_LOCATION_HAS_ACCURACY)) {
        if (location_cb) {
            location_cb( &r->fix );
            D("gps report: flag=%x, lat=%f, lon=%f, altitude=%f, bearing=%f, speed=%f, accuracy=%f", r->fix.flags,
               r->fix.latitude, r->fix.longitude, r->fix.altitude, r->fix.bearing, r->fix.speed, r->fix.accuracy);
            r->fix.flags = 0;
        }
        else {
            LOGE("loc_cb no callback!");
        }
    }
}


static void nmea_reader_addc( NmeaReader*  r, char  c )
{
    if (r->overflow) {
        r->overflow = (c != '\n');
        return;
    }

    if (r->pos >= (int) sizeof(r->in)-1 ) {
        r->overflow = 1;
        r->pos      = 0;
        return;
    }

    r->in[r->pos] = (char)c;
    r->pos       += 1;

    if (c == '\n') {
        nmea_reader_parse( r );
        r->pos = 0;
    }
}

static int SetAttr(int m_fd, int iSpeed, int iFlowCtl, int DataBits, int iStopBits, char iParity)
{ 
    int rVal	  = -1;
    int iSpeedDef = B9600;
    struct termios opt;  
 
    rVal = tcgetattr(m_fd, &opt);
    if (0 != rVal)
    { 
        LOGE("tcgetattr(fd:%d) err rVal:%d %s\n", m_fd, rVal, strerror(errno));
        return rVal;
    }

    switch (iSpeed) 
    {
        case 300:
            iSpeedDef = B300;
            break; 
        case 1200:
            iSpeedDef = B1200;
            break; 
        case 2400:
            iSpeedDef = B2400;
            break;
        case 4800:
            iSpeedDef = B4800;
            break; 
        case 9600:
            iSpeedDef = B9600;
            break; 
        case 19200:
            iSpeedDef = B19200;
            break; 
        case 38400:
            iSpeedDef = B38400;
            break; 
        case 115200:
            iSpeedDef = B115200;
            break; 
        default:
    LOGE("iSpeed:%d err(fd:%d)\n", iSpeed, m_fd);
    return -1; 
}
    cfsetispeed(&opt, iSpeedDef);
    cfsetospeed(&opt, iSpeedDef);
    opt.c_cflag |= CLOCAL;
    opt.c_cflag |= CREAD;
    switch (iFlowCtl) 
    {  
        case 0:
            opt.c_cflag &= ~CRTSCTS;
            break;
        case 1:
            opt.c_cflag |= CRTSCTS;
            break;
        case 2:
            opt.c_cflag |= IXON | IXOFF | IXANY;
            break; 
        default:
            LOGE("iFlowCtl:%d err(fd:%d)\n", iFlowCtl, m_fd);
            return -1;
    }

    opt.c_cflag &= ~CSIZE;   
    switch (DataBits) 
    {
        case 5:
            opt.c_cflag |= CS5;
            break; 
        case 6:
            opt.c_cflag |= CS6;
            break; 
        case 7:
            opt.c_cflag |= CS7;
            break;  
        case 8:
            opt.c_cflag |= CS8;
            break;   
        default: 
            LOGE("DataBits:%d err(fd:%d)\n", DataBits, m_fd);
            return -1;
    }  

    switch (iParity) 
    {
        case 'n':
        case 'N':
            opt.c_cflag &= ~PARENB;   
            opt.c_iflag &= ~INPCK;
            break; 
        case 'o': 
        case 'O':
            opt.c_cflag |= (PARODD | PARENB);	
            opt.c_iflag |= INPCK;
            break; 
        case 'e':
        case 'E':
            opt.c_cflag |= PARENB;   
            opt.c_cflag &= ~PARODD;
            opt.c_iflag |= INPCK; 
            break;
        case 's':  
        case 'S':
            opt.c_cflag &= ~PARENB;  
            opt.c_cflag &= ~CSTOPB;  
            break; 
        default:
            LOGE("iParity:%c err(fd:%d)\n", iParity, m_fd);
            return -1;  
    } 

    switch (iStopBits)
    {
        case 1:
            opt.c_cflag &= ~CSTOPB;
            break;
        case 2:
            opt.c_cflag |= CSTOPB;
            break;
        default:
            LOGE("iStopBits:%c err(fd:%d)\n", iStopBits, m_fd);
            return -1;   
    } 
    opt.c_oflag    &= ~OPOST;
    opt.c_lflag    &= ~(ICANON | ECHO | ECHOE | ISIG);
    opt.c_cc[VTIME] = 1; 
    opt.c_cc[VMIN]	= 1; 
    tcflush(m_fd, TCIFLUSH);

    rVal = tcsetattr(m_fd, TCSANOW, &opt);
    if (rVal != 0)
    {  
        return -1;  
    }

    return rVal;
}

static int loc_init(GpsCallbacks* callbacks)
{
    
    LOGE("Mingxin GPS init begin:%d \n", init);
 
    if (init != 0)
    {
        return 0;
    }

    gss_fd = open("/dev/ttyAMA1", O_RDONLY | O_NOCTTY | O_NDELAY | O_NONBLOCK);
    if (gss_fd < 0)
    {
        LOGE("Mingxin GPS open failed: %s\n", strerror(errno));
        goto fail_3;
    }

    if (fcntl(gss_fd, F_SETFL, 0) < 0)
    { 
        LOGE("fcntl(F_SETFL) err gss_fd:%d %s\n", gss_fd,  strerror(errno));
		goto fail_2;
    }

    if (SetAttr(gss_fd, 9600, 0, 8, 1, 'N') < 0 ) 
    {
        LOGE("fcntl(SetAttr) err gss_fd:%d %s\n", gss_fd,  strerror(errno));
		goto fail_2;
    }

    location_cb      = callbacks->location_cb;
    status_cb        = callbacks->status_cb;
    svstatus_cb      = callbacks->sv_status_cb;
    nmea_cb          = callbacks->nmea_cb;
    setcap_cb        = callbacks->set_capabilities_cb;
    acquire_lock_cb  = callbacks->acquire_wakelock_cb;
    rel_lock_cb      = callbacks->release_wakelock_cb;
    thread_cb        = callbacks->create_thread_cb;

    buff = (char*) malloc(BUFF_LEN);
    if (NULL == buff)
    {
        LOGE("gps init alloc buff failed\n");
		goto fail_2;
    }

    thread = thread_cb("gps_state_thread", gps_state_thread, NULL);
    if ( !thread ) {
        LOGE("could not create gps thread: %s", strerror(errno));
		goto fail_1;
    }
    init = 1;
    LOGE("Mingxin GPS init success!\n");
    return 0;

    fail_1:
    free(buff);	
	buff = NULL;
	fail_2:
	close(gss_fd);
	fail_3:
    gss_fd = -1;
    return -1;	
}

static int loc_start()
{
    LOGE("Mingxin GPS  start success!\n");
    return 0;
}

static int loc_stop()
{
    LOGE("Mingxin GPS  stop success!\n");
    return 0;
}

static void loc_cleanup()
{
	void*  dummy;

    if (init != 0)
    {
        pthread_join(thread, &dummy);
        close(gss_fd);
        gss_fd = -1;
        free(buff);
        buff = NULL;
        init = 0;
    }

    LOGE("Mingxin GPS  cleanup success!\n");
}

static int loc_inject_time(GpsUtcTime time, int64_t timeReference, int uncertainty)
{
    LOGE("Mingxin GPS  inject time\n");
    return 0;
}

static int loc_inject_location(double latitude, double longitude, float accuracy)
{
    LOGE("Mingxin GPS  inject location!\n");
    return 0;
}

static void loc_delete_aiding_data(GpsAidingData f)
{
    LOGE("Mingxin GPS  delete aiding data!\n");
}

const void* loc_get_extension(const char* name)
{
    return NULL;
}

static int	loc_set_position_mode(GpsPositionMode mode, GpsPositionRecurrence recurrence, uint32_t min_interval,uint32_t preferred_accuracy,uint32_t preferred_time)
{
    LOGE("Mingxin GPS  set position mode!\n");
    return 0;
}

static int epoll_register( int  epoll_fd, int  fd )
{
    struct epoll_event  ev;
    int                 ret, flags;

    /* important: make the fd non-blocking */
    flags = fcntl(fd, F_GETFL);
    fcntl(fd, F_SETFL, flags | O_NONBLOCK);

    ev.events  = EPOLLIN;
    ev.data.fd = fd;
    do {
        ret = epoll_ctl( epoll_fd, EPOLL_CTL_ADD, fd, &ev );
    } while (ret < 0 && errno == EINTR);
    return ret;
}


static int epoll_deregister( int  epoll_fd, int  fd )
{
    int  ret;
    do {
        ret = epoll_ctl( epoll_fd, EPOLL_CTL_DEL, fd, NULL );
    } while (ret < 0 && errno == EINTR);
    return ret;
}

static void gps_state_thread( void*  arg )
{
    //char  buff[32];
    NmeaReader  reader[1];
    int  epoll_fd   = epoll_create(1);

    nmea_reader_init( reader );
 
    epoll_register( epoll_fd, gss_fd );

    D("gps fd event begin");
    for (;;)
    {
        struct epoll_event   events;
        int    ne, nevents;

        nevents = epoll_wait( epoll_fd, &events, 1, -1 );
        if (nevents < 0)
        {
            if (errno != EINTR)
                LOGE("epoll_wait() unexpected error: %s", strerror(errno));
            break;
        }
        if ((events.events & (EPOLLERR|EPOLLHUP)) != 0)
        {
            LOGE("EPOLLERR or EPOLLHUP after epoll_wait() !?");
            break;
        }
        if ((events.events & EPOLLIN) != 0 && events.data.fd == gss_fd)
        {
            for (;;)
            {
				int  nn, ret;
                ret = read( gss_fd, buff, BUFF_LEN );
                if (ret < 0) 
                {
                    if (errno == EINTR)
                        continue;
                    if (errno != EWOULDBLOCK)
                        LOGE("error while reading from gps port: %s:", strerror(errno));
                    break;
                }

                for (nn = 0; nn < ret; nn++)
                { 
                    nmea_reader_addc(reader, buff[nn]);
                }
            }
        }
    }
    epoll_deregister( epoll_fd, gss_fd );

    D("gps fd event end");
}


const GpsInterface* gps__get_gps_interface(struct gps_device_t* dev)
{
    return &sLocEngInterface;
}

static int open_gps(const struct hw_module_t* module, char const* name,
        struct hw_device_t** device)
{
    struct gps_device_t *dev = malloc(sizeof(struct gps_device_t));
    memset(dev, 0, sizeof(*dev));

    dev->common.tag = HARDWARE_DEVICE_TAG;
    dev->common.version = 0;
    dev->common.module = (struct hw_module_t*)module;
    dev->get_gps_interface = gps__get_gps_interface;

    *device = (struct hw_device_t*)dev;
    return 0;
}


static struct hw_module_methods_t gps_module_methods = {
    .open = open_gps
};

struct hw_module_t HAL_MODULE_INFO_SYM = {
    .tag           = HARDWARE_MODULE_TAG,
    .version_major = 1,
    .version_minor = 0,
    .id            = GPS_HARDWARE_MODULE_ID,
    .name          = "Default GPS Module",
    .author        = "The Android Open Source Project",
    .methods       = &gps_module_methods,
};


