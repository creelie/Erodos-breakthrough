// independent check: all m <= MMAX with m = 1757 (mod 3510), m = +-1 (mod 8), 3511 !| m,
// and 2^(3511^2 m - 2) = 1 (mod m); plain 128-bit remainder arithmetic, right-to-left powering
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
int main(int argc,char**argv){
  u64 MMAX=strtoull(argv[1],0,10); int nth=atoi(argv[2]), id=atoi(argv[3]); long cnt=0;
  for(u64 t=id; ; t+=nth){
    u64 m=1757+3510*t; if(m>MMAX) break;
    if((m&7)!=1 && (m&7)!=7) continue;
    if(m%3511==0) continue;
    u128 e=(u128)12327121*m-2; u64 r=1%m, b=2%m;
    while(e){ if(e&1) r=(u64)(((u128)r*b)%m); b=(u64)(((u128)b*b)%m); e>>=1; }
    cnt++;
    if(r==1){ printf("%llu\n",(unsigned long long)m); fflush(stdout); }
  }
  fprintf(stderr,"thread %d tested %ld\n",id,cnt);
}
