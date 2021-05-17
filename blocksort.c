/* patch for bzip2-1.0.6 */

#include "bzlib_private.h"
#include "cyclic-sais.c"

void
BZ2_blockSort(EState *s) {
  int *freeblock;
  UInt32 *ptr = s->ptr;
  Int32 nblock = s->nblock, fs;
  Int32 i;
  int err;

  fs = (nblock * (sizeof(UInt32) - sizeof(UChar))) / sizeof(UInt32);
  if(fs <= 65537) {
    freeblock = (int *)(s->ftab);
    fs = 65537;
  } else {
    freeblock = (int *)(&(s->block[nblock]));
  }

  err = cyclic_sais_raw(s->block, (int *)ptr, freeblock, 0, fs,
                        nblock, 256, sizeof(unsigned char), 0);
  AssertH( err == 0, 1010 );
  s->origPtr = -1;
  for(i = 0; i < nblock; ++i) { if(ptr[i] == 0) { s->origPtr = i; } }

  AssertH( s->origPtr != -1, 1003 );
}
