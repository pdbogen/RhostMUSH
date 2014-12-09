#!/bin/bash
echo "This will pull a src tarball from the Server location and attempt to rebuild."
echo "Once fiished, you can @reboot in the Mush to load the new code."
echo "Do not forget to @readcache as well to read in the new text files."
echo ""
echo "Do you wish to attempt to update your source code now? (Y/N): "|tr -d '\012'
read ANS
if [ "${ANS}" = "Y" -o "${ANS}" = "y" ]
then
   echo "Rebuilding source tree... please wait..."
else
   echo "Abortng by user request."
   exit 1
fi
type=0
if [ -f ./src.tbz ]
then
   echo "I found a source file."
   ls -l src.tbz
   echo "Use this file? (Y/N): "|tr -d '\012'
   read ANS
   if [ "${ANS}" = "Y" -o "${ANS}" = "y" ]
   then
      echo "Ok, I'm rebuilding off that source file.  Hold on to your hat..."
   else
      echo "Verywell.  Please move/copy in the src.tbz file you wish to use in your $(pwd) directory."
      exit 1
   fi
else
   echo "Hum.  No source files.  I'll tell git to yoink the source files for you then."
   echo "downloading..."|tr -d '\012'
   git clone https://github.com/RhostMUSH/trunk rhost_tmp > /dev/null 2>&1
   echo "done!"
   type=1
fi
echo "Making a backup of all your files, please wait..."|tr -d '\012'
lc_date=$(date +%m%d%y%H%M%S)
tar -czf src_backup_${lc_date}.tgz src/*.c hdrs/*.h game/txt/help.txt game/txt/wizhelp.txt > /dev/null 2>&1
echo "... completed.  Filename is src_backup_${lc_date}.tgz"
echo "Copying your binary ... just in case.  Backup will be src/netrhost.automate (or bin/netrhost.automate)"
[[ -f src/netrhost ]] && cp -f src/netrhost src/netrhost.automate
[[ -f bin/netrhost ]] && cp -f bin/netrhost bin/netrhost.automate
if [ ${type} -eq 0 ]
then
   bunzip -cd src.tbz|tar -xvf -
else
   mv -f src/local.c src/local.c.backup
   cp -f rhost_tmp/Server/src/*.c src
   cp -f src/local.c.backup src/local.c
   cp -f rhost_tmp/Server/hdrs/*.h hdrs
   cp -f rhost_tmp/Server/bin/asksource* bin
   cp -f rhost_tmp/Server/game/txt/help.txt game/txt/help.txt
   cp -f rhost_tmp/Server/game/txt/wizhelp.txt game/txt/wizhelp.txt
   rm -rf ./rhost_tmp
fi
cd src
make clean;make
cd ../game/txt
../mkindx help.txt help.indx
../mkindx wizhelp.txt wizhelp.indx
echo "Ok, we're done.  Ignore any warnings.  If you had errors, please report it to the developers."
echo "Once you @reboot the mush, please issue @readcache to read in the new help files."
exit 0
