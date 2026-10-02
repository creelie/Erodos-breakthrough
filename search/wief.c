// list all primes p < LIMIT with 2^(p-1) ≡ 1 (mod p^2); segmented sieve, Montgomery mod p^2 (< 2^64)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static inline u64 minv(u64 m){ u64 x=m; for(int i=0;i<6;i++) x*=2-m*x; return -x; }
static inline u64 redc(u128 T,u64 m,u64 mi){ u64 q=(u64)T*mi; u128 qm=(u128)q*m; u128 s=T+qm; int c=s<T;
  u128 t=(s>>64)|((u128)c<<64); if(t>=m) t-=m; return (u64)t; }
static int wief(u64 p){ u64 m=p*p, mi=minv(m); u64 R=(u64)(((u128)1<<64)%m); u64 R2=(u64)(((u128)R*R)%m);
  u64 x=redc((u128)2*R2,m,mi), acc=R; u64 e=p-1; int top=63; while(!((e>>top)&1)) top--;
  for(int b=top;b>=0;b--){ acc=redc((u128)acc*acc,m,mi); if((e>>b)&1) acc=redc((u128)acc*x,m,mi);} return acc==R; }
int main(int argc,char**argv){
  u64 LIM=strtoull(argv[1],0,10); int nth=atoi(argv[2]), id=atoi(argv[3]);
  u64 sq=(u64)sqrtl((long double)LIM)+2; char*s=calloc(sq+1,1); u64 np=0; u64*pr=malloc(sizeof(u64)*sq);
  for(u64 i=2;i<=sq;i++) if(!s[i]){ pr[np++]=i; for(u64 j=i*i;j<=sq;j+=i) s[j]=1; }
  const u64 SEG=1<<22; char*seg=malloc(SEG); u64 cnt=0;
  for(u64 lo=SEG*id; lo<LIM; lo+=SEG*nth){
    u64 hi=lo+SEG; if(hi>LIM) hi=LIM; memset(seg,0,SEG);
    for(u64 k=0;k<np;k++){ u64 p=pr[k]; if(p*p>=hi) break; u64 st=(lo+p-1)/p*p; if(st<p*p) st=p*p; for(u64 j=st;j<hi;j+=p) seg[j-lo]=1; }
    for(u64 v=(lo<3?3:lo|1); v<hi; v+=2) if(!seg[v-lo]){ cnt++; if(wief(v)) { printf("WIEFERICH %llu\n",(unsigned long long)v); fflush(stdout);} }
  }
  fprintf(stderr,"thread %d odd primes tested %llu\n",id,(unsigned long long)cnt);
}
