#define Is_uint63(v) (Is_long(v))

#define uint_of_value(val) (((uint64_t)(val)) >> 1)
#define uint63_of_value(val) ((uint64_t)(val) >> 1)

/* 2^63 * y + x as a value */
//#define Val_intint(x,y) ((value)(((uint64_t)(x)) << 1 + ((uint64_t)(y) << 64)))

#define uint63_zero ((value) 1) /* 2*0 + 1 */
#define uint63_one() ((value) 3) /* 2*1 + 1 */

#define uint63_eq(x,y) ((x) == (y))
#define Uint63_eq(r,x,y) ((r) = uint63_eq(x,y))
#define Uint63_eq0(r,x) ((r) = ((x) == (uint64_t)1))
#define uint63_lt(x,y) ((uint64_t) (x) < (uint64_t) (y))
#define Uint63_lt(r,x,y) ((r) = uint63_lt(x,y))
#define uint63_leq(x,y) ((uint64_t) (x) <= (uint64_t) (y))
#define Uint63_leq(r,x,y) ((r) = uint63_leq(x,y))

#define Uint63_add(x,y) (accu = (value)((uint64_t) (x) + (uint64_t) (y) - 1))
#define Uint63_addcarry(x,y) (accu = (value)((uint64_t) (x) + (uint64_t) (y) + 1))
#define Uint63_sub(x,y) (accu = (value)((uint64_t) (x) - (uint64_t) (y) + 1))
#define Uint63_subcarry(x,y) (accu = (value)((uint64_t) (x) - (uint64_t) (y) - 1))
#define Uint63_mul(x,y) (accu = Val_long(uint63_of_value(x) * uint63_of_value(y)))
#define Uint63_div(x,y) (accu = Val_long(uint63_of_value(x) / uint63_of_value(y)))
#define Uint63_mod(x,y) (accu = Val_long(uint63_of_value(x) % uint63_of_value(y)))

#define Uint63_lxor(x,y) (accu = (value)(((uint64_t)(x) ^ (uint64_t)(y)) | 1))
#define Uint63_lor(x,y) (accu = (value)((uint64_t)(x) | (uint64_t)(y)))
#define Uint63_land(x,y) (accu = (value)((uint64_t)(x) & (uint64_t)(y)))

/* TODO: is + or | better? OCAML uses + */
/* TODO: is - or ^ better? */
#define Uint63_lsl(x,y) do{ \
  value uint63_lsl_y__ = (y); \
  if (uint63_lsl_y__ < (uint64_t) 127) \
    accu = (value)((((uint64_t)(x)-1) << uint63_of_value(uint63_lsl_y__)) | 1); \
  else \
    accu = uint63_zero; \
  }while(0)
#define Uint63_lsr(x,y) do{ \
  value uint63_lsl_y__ = (y); \
  if (uint63_lsl_y__ < (uint64_t) 127) \
    accu = (value)(((uint64_t)(x) >> uint63_of_value(uint63_lsl_y__)) | 1); \
  else \
    accu = uint63_zero; \
  }while(0)
#define Uint63_lsl1(x) (accu = (value)((((uint64_t)(x)-1) << 1) +1))
#define Uint63_lsr1(x) (accu = (value)(((uint64_t)(x) >> 1) |1))

/* addmuldiv(p,x,y) = x * 2^p + y / 2 ^ (63 - p) */
/* (modulo 2^63) for p <= 63 */
value uint63_addmuldiv(uint64_t p, uint64_t x, uint64_t y) {
  uint64_t shiftby = uint63_of_value(p);
  value r = (value)((uint64_t)(x^1) << shiftby);
  r |= ((uint64_t)y >> (63-shiftby)) | 1;
  return r;
}
#define Uint63_addmuldiv(p, x, y) (accu = uint63_addmuldiv(p, x, y))

value uint63_head0(uint64_t x) {
  int r = 0;
  if (!(x & 0xFFFFFFFF00000000)) { x <<= 32; r += 32; }
  if (!(x & 0xFFFF000000000000)) { x <<= 16; r += 16; }
  if (!(x & 0xFF00000000000000)) { x <<= 8;  r += 8; }
  if (!(x & 0xF000000000000000)) { x <<= 4;  r += 4; }
  if (!(x & 0xC000000000000000)) { x <<= 2;  r += 2; }
  if (!(x & 0x8000000000000000)) { x <<=1;   r += 1; }
  return Val_int(r);
}
#define Uint63_head0(x) (accu = uint63_head0(x))

value uint63_tail0(value x) {
  int r = 0;
  x = (uint64_t)x >> 1;
  if (!(x & 0xFFFFFFFF)) { x >>= 32; r += 32; }
  if (!(x & 0x0000FFFF)) { x >>= 16; r += 16; }
  if (!(x & 0x000000FF)) { x >>= 8;  r += 8; }
  if (!(x & 0x0000000F)) { x >>= 4;  r += 4; }
  if (!(x & 0x00000003)) { x >>= 2;  r += 2; }
  if (!(x & 0x00000001)) { x >>=1;   r += 1; }
  return Val_int(r);
}
#define Uint63_tail0(x) (accu = uint63_tail0(x))

value uint63_mulc(value x, value y, value* h) {
  x = (uint64_t)x >> 1;
  y = (uint64_t)y >> 1;
  uint64_t lx = x & 0xFFFFFFFF;
  uint64_t ly = y & 0xFFFFFFFF;
  uint64_t hx = x >> 32;
  uint64_t hy = y >> 32;
  uint64_t hr = hx * hy;
  uint64_t lr = lx * ly;
  lx *= hy;
  ly *= hx;
  hr += (lx >> 32) + (ly >> 32);
  lx <<= 32;
  lr += lx;
  if (lr < lx) { hr++; }
  ly <<= 32;
  lr += ly;
  if (lr < ly) { hr++; }
  hr = (hr << 1) | (lr >> 63);
  *h = Val_int(hr);
  return Val_int(lr);
}
#define Uint63_mulc(x, y, h) (accu = uint63_mulc(x, y, h))

#define lt128(xh,xl,yh,yl) (uint63_lt(xh,yh) || (uint63_eq(xh,yh) && uint63_lt(xl,yl)))
#define le128(xh,xl,yh,yl) (uint63_lt(xh,yh) || (uint63_eq(xh,yh) && uint63_leq(xl,yl)))

#define maxuint63 ((uint64_t)0x7FFFFFFFFFFFFFFF)
/* precondition: y <> 0 */
/* outputs r and sets ql to q % 2^63 s.t. x = q * y + r, r < y */
static value uint63_div21_aux(value xh, value xl, value y, value* ql) {
  xh = uint63_of_value(xh);
  xl = uint63_of_value(xl);
  y = uint63_of_value(y);
  uint64_t maskh = 0;
  uint64_t maskl = 1;
  uint64_t dh = 0;
  uint64_t dl = y;
  int cmp = 1;
  /* int n = 0 */
  /* loop invariant: mask = 2^n, d = mask * y, (2 * d <= x -> cmp), n >= 0, d < 2^(2*63) */
  while (!(dh >> (63 - 1)) && cmp) {
    dh = (dh << 1) | (dl >> (63 - 1));
    dl = (dl << 1) & maxuint63;
    maskh = (maskh << 1) | (maskl >> (63 - 1));
    maskl = (maskl << 1) & maxuint63;
    /* ++n */
    cmp = lt128(dh,dl,xh,xl);
  }
  uint64_t remh = xh;
  uint64_t reml = xl;
  /* uint64_t quotienth = 0; */
  uint64_t quotientl = 0;
  /* loop invariant: x = quotient * y + rem, y * 2^(n+1) > r,
     mask = floor(2^n), d = mask * y, n >= -1 */
  while (maskh | maskl) {
    if (le128(dh,dl,remh,reml)) { /* if rem >= d, add one bit and subtract d */
      /* quotienth = quotienth | maskh */
      quotientl = quotientl | maskl;
      remh = (uint63_lt(reml,dl)) ? (remh - dh - 1) : (remh - dh);
      reml = (reml - dl) & maxuint63;
    }
    maskl = (maskl >> 1) | ((maskh << (63 - 1)) & maxuint63);
    maskh = maskh >> 1;
    dl = (dl >> 1) | ((dh << (63 - 1)) & maxuint63);
    dh = dh >> 1;
    /* decr n */
  }
  *ql = Val_int(quotientl);
  return Val_int(reml);
}
value uint63_div21(value xh, value xl, value y, value* ql) {
  if (uint63_of_value(y) == 0) {
    *ql = Val_int(0);
    return Val_int(0);
  } else {
    return uint63_div21_aux(xh, xl, y, ql);
  }
}
#define Uint63_div21(xh, xl, y, q) (accu = uint63_div21(xh, xl, y, q))
