#include <stdio.h>
static inline unsigned u8step(unsigned s, unsigned b) {
  switch (s) {
    case 0: if (b < 0x80) return 0; if (b < 0xC2) return 8; if (b < 0xE0) return 1; if (b == 0xE0) return 4; if (b == 0xED) return 5; if (b < 0xF0) return 2;
            if (b == 0xF0) return 6;
            if (b < 0xF4) return 3; if (b == 0xF4) return 7; return 8;
    case 1: case 2: case 3: return (b >= 0x80 && b < 0xC0) ? s - 1 : 8;
    case 4: return (b >= 0xA0 && b < 0xC0) ? 1 : 8;
    case 5: return (b >= 0x80 && b < 0xA0) ? 1 : 8;
    case 6: return (b >= 0x90 && b < 0xC0) ? 2 : 8;
    case 7: return (b >= 0x80 && b < 0x90) ? 2 : 8;
    default: return 8;
  }
}
int main(void){ long c[5]={0}; 
 for (unsigned l=1;l<=4;l++){ unsigned long total=1UL<<(8*l); for(unsigned long v=0;v<total;v++){ unsigned s=0; int ok=1; for(unsigned j=0;j<l;j++){ unsigned b=(v>>(8*j))&255; s=u8step(s,b); if(s==8){ok=0;break;} } if(ok&&s==0){ // must also end exactly at last byte: check no earlier accept (s==0 before end)
   unsigned s2=0; int early=0; for(unsigned j=0;j<l;j++){ unsigned b=(v>>(8*j))&255; s2=u8step(s2,b); if(s2==0&&j<l-1){early=1;break;} } if(!early) c[l]++; } } }
 printf("%ld %ld %ld %ld\n",c[1],c[2],c[3],c[4]); }
