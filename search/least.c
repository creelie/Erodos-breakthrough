// least m (odd, m ≡ 2 mod 1755, m ≡ ±1 mod 8) with 2^(3511^2*m-2) ≡ 1 (mod m)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static inline u64 mont_inv(u64 m){ u64 x=m; for(int i=0;i<6;i++) x*=2-m*x; return -x; } // -m^{-1} mod 2^64
static inline u64 redc(u128 T,u64 m,u64 mi){ u64 q=(u64)T*mi; u128 t=(T+(u128)q*m)>>64; return t>=m? (u64)(t-m):(u64)t; }
int main(int argc,char**argv){
  u64 MMAX=strtoull(argv[1],0,10); int nth=atoi(argv[2]); int id=atoi(argv[3]);
  const u64 P2=12327121ULL; // 3511^2
  // m ≡ 1757 mod 3510 (m ≡ 2 mod 1755, odd); m ≡ 1 or 7 mod 8 -> combine mod 14040
  long cnt=0;
  for(u64 base=0; base<=MMAX; base+=14040ULL*nth){
    for(u64 off=0; off<14040; off+=3510){
      u64 m=base+14040ULL*id+1757+off; if(m>MMAX) break;
      u64 r8=m&7; if(r8!=1 && r8!=7) continue;
      // compute 2^(P2*m-2) mod m via Montgomery
      u128 e=(u128)P2*m-2;
      u64 mi=mont_inv(m);
      u64 R=(u64)(((u128)1<<64)%m); // R mod m
      u64 R2=(u64)(((u128)R*R)%m);
      u64 x=redc((u128)2*R2,m,mi); // 2 in Montgomery form? redc(2*R2)=2R mod m
      u64 acc=R; // 1 in Montgomery form
      // left-to-right binary exponentiation
      int top=127; while(top>=0 && !((e>>top)&1)) top--;
      for(int b=top;b>=0;b--){
        acc=redc((u128)acc*acc,m,mi);
        if((e>>b)&1) acc=redc((u128)acc*x,m,mi);
      }
      if(acc==R && m%3511ULL!=0){ printf("m=%llu n=%s\n",(unsigned long long)m,""); fflush(stdout); }
      cnt++;
    }
  }
  fprintf(stderr,"thread %d checked %ld\n",id,cnt);
}
