#ifdef RHOST_MYSQL

#include <mysql.h>
#include <unistd.h>
#include <regex.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>
#include <dirent.h>
#include <time.h>

#include "copyright.h"
#include "autoconf.h"

#include "config.h"
#include "db.h"
#include "interface.h"
#include "mudconf.h"
#include "command.h"
#include "functions.h"
#include "externs.h"
#include "match.h"
#include "flags.h"
#include "alloc.h"
#include "vattr.h"

#define MYSQL_POOL_SIZE 10

#ifdef DEBUG_MYSQL
	#define DEBUG_MYSQL(m) LOG_SIMPLE( LOG_ALWAYS, "MSQ", "DEBUG", m )
#else
	#define DEBUG_MYSQL(m)
#endif


int rhost_mysql_validate_username( char * username, char **p_buff, char ***p_bufcx );
int rhost_mysql_validate_hostname( char * hostname, char **p_buff, char ***p_bufcx );
MYSQL * rhost_mysql_connect( const char * hostname, const char * username, const char * password, const char * database, char **p_buff, char ***p_bufcx );

static char tempbuff[LBUF_SIZE];
static char tempbuff2[LBUF_SIZE];

static int ival(char *buff, char **bufcx, int result) {
   sprintf(tempbuff, "%d", result);
   safe_str(tempbuff, buff, bufcx);
   return 0;
}

typedef enum {
	unused,
	opened,
} mysql_status;

typedef struct mysql_pool_entry {
	MYSQL * connection;
	mysql_status status;
	char hostname[LBUF_SIZE],
	     username[LBUF_SIZE],
	     password[LBUF_SIZE],
	     database[LBUF_SIZE];
	time_t last_used;
} mysql_pool_entry;

static mysql_pool_entry mysql_pool[MYSQL_POOL_SIZE];

FUNCTION(local_fun_mysql_query)
{
   time_t start;
   char dbFile[LBUF_SIZE], dbFullPath[LBUF_SIZE];
   char * colPtr, *zTail;
   MYSQL * mysql_db;
   MYSQL_STMT * mysql_stmt;
   unsigned int i, rVal, firstA=1, firstB=1, argIdx, argCount;
   char colDelimit[LBUF_SIZE], rowDelimit[LBUF_SIZE];

   char *hostname, *username, *password, *database, *query;

   if ( mudstate.heavy_cpu_lockdown == 1 ) {
      safe_str("#-1 FUNCTION HAS BEEN LOCKED DOWN FOR HEAVY CPU USE.", buff, bufcx);
      return;
   }

   if( nfargs < 5 ) {
      safe_str( "#-1 FUNCTION (mysql_query) EXPECTS 5 OR MORE ARGUMENTS [RECEIVED ", buff, bufcx );
      ival( buff, bufcx, nfargs );
      safe_chr( ']', buff, bufcx );
      return;
   }

   hostname = fargs[0];
   username = fargs[1];
   password = fargs[2];
   database = fargs[3];
   query    = fargs[4];

   if ( mudstate.heavy_cpu_tmark2 > (mudstate.heavy_cpu_tmark1 + mudconf.cputimechk) ) {
      safe_str("#-1 HEAVY CPU LIMIT ON PROTECTED FUNCTION EXCEEDED", buff, bufcx);
      mudstate.chkcpu_toggle = 1;
      mudstate.heavy_cpu_recurse = mudconf.heavy_cpu_max + 1;
      if ( mudstate.heavy_cpu_tmark2 > (mudstate.heavy_cpu_tmark1 + (mudconf.cputimechk * 3)) ) {
         mudstate.heavy_cpu_lockdown = 1;
      }
      return;
   }

   mudstate.heavy_cpu_tmark2 = time(NULL);

   if( nfargs >= 6 ) {
      strncpy( colDelimit, fargs[5], LBUF_SIZE );
      if( nfargs >= 7 ) {
         strncpy( rowDelimit, fargs[6], LBUF_SIZE );
      }
   } else {
      strcpy( colDelimit, "|" );
      strcpy( rowDelimit, "^" );
   }

   // http://dev.mysql.com/doc/refman/4.1/en/user-names.html
   // http://tools.ietf.org/html/rfc1035
   // A username of 1-16 characters, optionally followed by a colon, followed by
   // a password of unlimited length, followed by an @ sign, followed by a hostname
   // A hostname is a list of .-separated labels; each label is a letter followed by up to 62 letters, digits, or hyphens

   if( !rhost_mysql_validate_hostname( hostname, &buff, &bufcx ) ) {
     return;
   }

   if( !rhost_mysql_validate_username( username, &buff, &bufcx ) ) {
     return;
   }

	DEBUG_MYSQL( "Done!" );
	DEBUG_MYSQL( "Open database.." );

	mysql_db = rhost_mysql_connect( hostname, username, password, database, &buff, &bufcx );

   return;
}

void local_mysql_init(void) {
   FUN *fp;
   char *buff, *cp, *dp;
   struct stat sb;
   unsigned int i;

	DEBUG_MYSQL( "Initializing MySQL framework" );

   static FUN mysql_fun_table[] = {
      {"MYSQL_QUERY", local_fun_mysql_query, 0, FN_VARARGS, CA_WIZARD, 0 },
      {NULL, NULL, 0, 0, 0, 0}
   };

/* Register the functions */
   buff = alloc_sbuf("init_mysql_functab");
   for (fp = mysql_fun_table ; fp->name ; fp++) {
      cp = (char *) fp->name;
      dp = buff;
      while (*cp) {
         *dp = ToLower(*cp);
         cp++;
         dp++;
      }
      *dp = '\0';
      hashadd2(buff, (int *) fp, &mudstate.func_htab, 1);
   }

   // Initialize connection pool
   for( i = 0; i < MYSQL_POOL_SIZE; i++ ) {
      mysql_pool[i].status     = unused;
      mysql_pool[i].connection = NULL;
      memset( mysql_pool[i].hostname, 0, LBUF_SIZE );
      memset( mysql_pool[i].username, 0, LBUF_SIZE );
      memset( mysql_pool[i].password, 0, LBUF_SIZE );
      mysql_pool[i].last_used = 0;
   }
}

int rhost_mysql_validate_username( char * username, char **p_buff, char ***p_bufcx ) {
	DEBUG_MYSQL( "Validating username.." );
   unsigned int n = strnlen( username, LBUF_SIZE );
   if( n > 16 || n < 1 ) {
     safe_str( "#-1 FUNCTION (mysql_query) SECOND (username) ARGUMENT MUST BE 1 TO 16 CHARACTERS [RECEIVED ", *p_buff, *p_bufcx );
     ival( *p_buff, *p_bufcx, n );
     safe_chr( ']', *p_buff, *p_bufcx );
     DEBUG_MYSQL( "Failed!" );
     return 0;
   }
   DEBUG_MYSQL( "Done!" );
   return 1;
}

int rhost_mysql_validate_hostname( char * hostname, char **p_buff, char ***p_bufcx ) {
	DEBUG_MYSQL( "Validating hostname..." );
   // Validate hostname
   regex_t validator;
   regcomp( &validator, "^(([a-z][a-z0-9-]*)(\\.[a-z][a-z0-9-]*)*)|([0-9]+\\.[0-9]+\\.[0-9]+\\.[0-9]+)$", REG_EXTENDED | REG_NOSUB | REG_ICASE );
   if( regexec( &validator, hostname, 0, NULL, 0 ) != 0 ) {
      safe_str( "#-1 FUNCTION (mysql_query) FIRST ARGUMENT (hostname) MUST BE DOMAIN NAME OR IP ADDRESS [RECEIVED ", *p_buff, *p_bufcx );
      safe_str( hostname, *p_buff, *p_bufcx );
      safe_chr( ']', *p_buff, *p_bufcx );
      regfree( &validator );
      DEBUG_MYSQL( "Failed!" );
      return 0;
   }
   regfree( &validator );
   DEBUG_MYSQL( "Done!" );
   return 1;
}

MYSQL * rhost_mysql_connect( const char * hostname, const char * username, const char * password, const char * database, char **p_buff, char ***p_bufcx ) {
   mysql_pool_entry * poolEntry = NULL;
   MYSQL * result;
   unsigned int i = 0;

   DEBUG_MYSQL( "Beginning connection process..." );

   // FIXME: Look for existing connection

   // Look for free slot
   if( poolEntry == NULL ) {
      for( i = 0; i < MYSQL_POOL_SIZE; i++ ) {
         if( mysql_pool[i].status == unused ) {
            snprintf( tempbuff, LBUF_SIZE, "Located unused pool slot %d", i );
            DEBUG_MYSQL( tempbuff );
            poolEntry = &mysql_pool[i];
            break;
         }
      }
   }

   // FIXME: Free oldest slot

   // Connect
   if( poolEntry == NULL ) {
      safe_str( "#-1 FUNCTION (mysql_query) FAILED TO LOCATE AVAILABLE CONNECTION POOL SLOT. THIS SHOULD NOT HAPPEN.", *p_buff, *p_bufcx );
      return NULL;
   }

   poolEntry->connection = mysql_init(NULL);

   if( poolEntry->connection == NULL ) {
      safe_str( "#-1 FUNCTION (mysql_query) FAILED TO INITIALIZE MYSQL CONNECTION. THIS IS A MAJOR PROBLEM.", *p_buff, *p_bufcx );
      return NULL;
   }

   strncpy( poolEntry->hostname, hostname, LBUF_SIZE );
   strncpy( poolEntry->password, password, LBUF_SIZE );
   strncpy( poolEntry->username, username, LBUF_SIZE );
   strncpy( poolEntry->database, database, LBUF_SIZE );

   result = mysql_real_connect( poolEntry->connection,
                                poolEntry->hostname,
                                poolEntry->username,
                                poolEntry->password,
                                poolEntry->database,
                                0, // FIXME: port
                                NULL,
                                CLIENT_MULTI_STATEMENTS
   );

   if( result == NULL ) {
     snprintf( tempbuff, LBUF_SIZE, "#-1 FUNCTION (mysql_query) FAILED TO CONNECT: %s", mysql_error( poolEntry->connection ) );
     safe_str( tempbuff, *p_buff, *p_bufcx );
     DEBUG_MYSQL( "Failed to connect" );
     DEBUG_MYSQL( (char*) mysql_error( poolEntry->connection ) );
     mysql_close( poolEntry->connection );
     return NULL;
   }

   poolEntry->status = opened;
   DEBUG_MYSQL( "Connected!" );
   return poolEntry->connection;
}

#endif // RHOST_MYSQL
