static void fesquare(uint64_t out[5], const uint64_t in1[5]) {
  { const uint64_t x7 = in1[4];
  { const uint64_t x8 = in1[3];
  { const uint64_t x6 = in1[2];
  { const uint64_t x4 = in1[1];
  { const uint64_t x2 = in1[0];
  { uint128_t x9 = (((uint128_t)x2 * x7) + ((0x2 * ((uint128_t)x4 * x8)) + ((0x2 * ((uint128_t)x6 * x6)) + ((0x2 * ((uint128_t)x8 * x4)) + ((uint128_t)x7 * x2)))));
  { ℤ x10 = ((((uint128_t)x2 * x8) + ((0x2 * ((uint128_t)x4 * x6)) + ((0x2 * ((uint128_t)x6 * x4)) + ((uint128_t)x8 * x2)))) +ℤ ((0x3d1 * ((uint128_t)x7 * x7)) +ℤ (0x100000000 *ℤ ((uint128_t)x7 * x7))));
  { ℤ x11 = ((((uint128_t)x2 * x6) + ((0x2 * ((uint128_t)x4 * x4)) + ((uint128_t)x6 * x2))) +ℤ ((0x3d1 * (((uint128_t)x8 * x7) + ((uint128_t)x7 * x8))) +ℤ (0x100000000 *ℤ (((uint128_t)x8 * x7) + ((uint128_t)x7 * x8)))));
  { ℤ x12 = ((((uint128_t)x2 * x4) + ((uint128_t)x4 * x2)) +ℤ ((0x3d1 * (((uint128_t)x6 * x7) + (((uint128_t)x8 * x8) + ((uint128_t)x7 * x6)))) +ℤ (0x100000000 *ℤ (((uint128_t)x6 * x7) + (((uint128_t)x8 * x8) + ((uint128_t)x7 * x6))))));
  { ℤ x13 = (((uint128_t)x2 * x2) +ℤ ((0x3d1 * ((0x2 * ((uint128_t)x4 * x7)) + ((0x2 * ((uint128_t)x6 * x8)) + ((0x2 * ((uint128_t)x8 * x6)) + (0x2 * ((uint128_t)x7 * x4)))))) +ℤ (0x100000000 *ℤ ((0x2 * ((uint128_t)x4 * x7)) + ((0x2 * ((uint128_t)x6 * x8)) + ((0x2 * ((uint128_t)x8 * x6)) + (0x2 * ((uint128_t)x7 * x4))))))));
  { uint64_t x14 = (uint64_t) (x9 >> 0x33);
  { uint64_t x15 = ((uint64_t)x9 & 0x7ffffffffffff);
  { uint128_t x16 = (((uint128_t)0x8000000000000 * x14) + x15);
  { uint64_t x17 = (uint64_t) (x16 >> 0x33);
  { uint64_t x18 = ((uint64_t)x16 & 0x7ffffffffffff);
  { uint128_t x19 = (((uint128_t)0x8000000000000 * x17) + x18);
  { uint64_t x20 = (uint64_t) (x19 >> 0x33);
  { uint64_t x21 = ((uint64_t)x19 & 0x7ffffffffffff);
  { ℤ x22 = (x13 +ℤ (((uint128_t)0x3d1 * x20) + ((uint128_t)0x100000000 * x20)));
  { uint128_t x23 = (x22 >> 0x34);
  { uint64_t x24 = (x22 & 0xfffffffffffff);
  { ℤ x25 = (x23 +ℤ x12);
  { uint128_t x26 = (x25 >> 0x33);
  { uint64_t x27 = (x25 & 0x7ffffffffffff);
  { ℤ x28 = (x26 +ℤ x11);
  { uint128_t x29 = (x28 >> 0x33);
  { uint64_t x30 = (x28 & 0x7ffffffffffff);
  { ℤ x31 = (x29 +ℤ x10);
  { uint128_t x32 = (x31 >> 0x33);
  { uint64_t x33 = (x31 & 0x7ffffffffffff);
  { uint128_t x34 = (x32 + x21);
  { uint64_t x35 = (uint64_t) (x34 >> 0x33);
  { uint64_t x36 = ((uint64_t)x34 & 0x7ffffffffffff);
  { uint128_t x37 = (x24 + ((0x3d1 * x35) + ((uint128_t)0x100000000 * x35)));
  { uint64_t x38 = (uint64_t) (x37 >> 0x34);
  { uint64_t x39 = ((uint64_t)x37 & 0xfffffffffffff);
  { uint64_t x40 = (x39 >> 0x34);
  { uint64_t x41 = (x39 & 0xfffffffffffff);
  out[0] = x41;
  out[1] = (x40 + (x38 + x27));
  out[2] = x30;
  out[3] = x33;
  out[4] = x36;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}