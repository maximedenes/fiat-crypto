static void femul(uint64_t out[6], const uint64_t in1[6], const uint64_t in2[6]) {
  { const uint64_t x12 = in1[5];
  { const uint64_t x13 = in1[4];
  { const uint64_t x11 = in1[3];
  { const uint64_t x9 = in1[2];
  { const uint64_t x7 = in1[1];
  { const uint64_t x5 = in1[0];
  { const uint64_t x22 = in2[5];
  { const uint64_t x23 = in2[4];
  { const uint64_t x21 = in2[3];
  { const uint64_t x19 = in2[2];
  { const uint64_t x17 = in2[1];
  { const uint64_t x15 = in2[0];
  { uint64_t x26;  uint64_t x25 = _mulx_u64(x5, x15, &x26);
  { uint64_t x29;  uint64_t x28 = _mulx_u64(x5, x17, &x29);
  { uint64_t x32;  uint64_t x31 = _mulx_u64(x5, x19, &x32);
  { uint64_t x35;  uint64_t x34 = _mulx_u64(x5, x21, &x35);
  { uint64_t x38;  uint64_t x37 = _mulx_u64(x5, x23, &x38);
  { uint64_t x41;  uint64_t x40 = _mulx_u64(x5, x22, &x41);
  { uint64_t x43; uint8_t x44 = _addcarryx_u64(0x0, x26, x28, &x43);
  { uint64_t x46; uint8_t x47 = _addcarryx_u64(x44, x29, x31, &x46);
  { uint64_t x49; uint8_t x50 = _addcarryx_u64(x47, x32, x34, &x49);
  { uint64_t x52; uint8_t x53 = _addcarryx_u64(x50, x35, x37, &x52);
  { uint64_t x55; uint8_t x56 = _addcarryx_u64(x53, x38, x40, &x55);
  { uint64_t x58; uint8_t _ = _addcarryx_u64(0x0, x56, x41, &x58);
  { uint64_t x62;  uint64_t x61 = _mulx_u64(x25, 0xffffffffffffffffL, &x62);
  { uint64_t x65;  uint64_t x64 = _mulx_u64(x25, 0xffffffffffffffffL, &x65);
  { uint64_t x68;  uint64_t x67 = _mulx_u64(x25, 0xfffffffdffffffffL, &x68);
  { uint64_t x71;  uint64_t x70 = _mulx_u64(x25, 0xffffffffffffffffL, &x71);
  { uint64_t x74;  uint64_t x73 = _mulx_u64(x25, 0xffffffffffffffffL, &x74);
  { uint8_t x77;  uint64_t x76 = _mulx_u64_out_u8(x25, 0x3, &x77);
  { uint64_t x79; uint8_t x80 = _addcarryx_u64(0x0, x62, x64, &x79);
  { uint64_t x82; uint8_t x83 = _addcarryx_u64(x80, x65, x67, &x82);
  { uint64_t x85; uint8_t x86 = _addcarryx_u64(x83, x68, x70, &x85);
  { uint64_t x88; uint8_t x89 = _addcarryx_u64(x86, x71, x73, &x88);
  { uint64_t x91; uint8_t x92 = _addcarryx_u64(x89, x74, x76, &x91);
  { uint8_t x93 = (x92 + x77);
  { uint64_t _; uint8_t x96 = _addcarryx_u64(0x0, x25, x61, &_);
  { uint64_t x98; uint8_t x99 = _addcarryx_u64(x96, x43, x79, &x98);
  { uint64_t x101; uint8_t x102 = _addcarryx_u64(x99, x46, x82, &x101);
  { uint64_t x104; uint8_t x105 = _addcarryx_u64(x102, x49, x85, &x104);
  { uint64_t x107; uint8_t x108 = _addcarryx_u64(x105, x52, x88, &x107);
  { uint64_t x110; uint8_t x111 = _addcarryx_u64(x108, x55, x91, &x110);
  { uint64_t x113; uint8_t x114 = _addcarryx_u64(x111, x58, x93, &x113);
  { uint64_t x117;  uint64_t x116 = _mulx_u64(x7, x15, &x117);
  { uint64_t x120;  uint64_t x119 = _mulx_u64(x7, x17, &x120);
  { uint64_t x123;  uint64_t x122 = _mulx_u64(x7, x19, &x123);
  { uint64_t x126;  uint64_t x125 = _mulx_u64(x7, x21, &x126);
  { uint64_t x129;  uint64_t x128 = _mulx_u64(x7, x23, &x129);
  { uint64_t x132;  uint64_t x131 = _mulx_u64(x7, x22, &x132);
  { uint64_t x134; uint8_t x135 = _addcarryx_u64(0x0, x117, x119, &x134);
  { uint64_t x137; uint8_t x138 = _addcarryx_u64(x135, x120, x122, &x137);
  { uint64_t x140; uint8_t x141 = _addcarryx_u64(x138, x123, x125, &x140);
  { uint64_t x143; uint8_t x144 = _addcarryx_u64(x141, x126, x128, &x143);
  { uint64_t x146; uint8_t x147 = _addcarryx_u64(x144, x129, x131, &x146);
  { uint64_t x149; uint8_t _ = _addcarryx_u64(0x0, x147, x132, &x149);
  { uint64_t x152; uint8_t x153 = _addcarryx_u64(0x0, x98, x116, &x152);
  { uint64_t x155; uint8_t x156 = _addcarryx_u64(x153, x101, x134, &x155);
  { uint64_t x158; uint8_t x159 = _addcarryx_u64(x156, x104, x137, &x158);
  { uint64_t x161; uint8_t x162 = _addcarryx_u64(x159, x107, x140, &x161);
  { uint64_t x164; uint8_t x165 = _addcarryx_u64(x162, x110, x143, &x164);
  { uint64_t x167; uint8_t x168 = _addcarryx_u64(x165, x113, x146, &x167);
  { uint64_t x170; uint8_t x171 = _addcarryx_u64(x168, x114, x149, &x170);
  { uint64_t x174;  uint64_t x173 = _mulx_u64(x152, 0xffffffffffffffffL, &x174);
  { uint64_t x177;  uint64_t x176 = _mulx_u64(x152, 0xffffffffffffffffL, &x177);
  { uint64_t x180;  uint64_t x179 = _mulx_u64(x152, 0xfffffffdffffffffL, &x180);
  { uint64_t x183;  uint64_t x182 = _mulx_u64(x152, 0xffffffffffffffffL, &x183);
  { uint64_t x186;  uint64_t x185 = _mulx_u64(x152, 0xffffffffffffffffL, &x186);
  { uint8_t x189;  uint64_t x188 = _mulx_u64_out_u8(x152, 0x3, &x189);
  { uint64_t x191; uint8_t x192 = _addcarryx_u64(0x0, x174, x176, &x191);
  { uint64_t x194; uint8_t x195 = _addcarryx_u64(x192, x177, x179, &x194);
  { uint64_t x197; uint8_t x198 = _addcarryx_u64(x195, x180, x182, &x197);
  { uint64_t x200; uint8_t x201 = _addcarryx_u64(x198, x183, x185, &x200);
  { uint64_t x203; uint8_t x204 = _addcarryx_u64(x201, x186, x188, &x203);
  { uint8_t x205 = (x204 + x189);
  { uint64_t _; uint8_t x208 = _addcarryx_u64(0x0, x152, x173, &_);
  { uint64_t x210; uint8_t x211 = _addcarryx_u64(x208, x155, x191, &x210);
  { uint64_t x213; uint8_t x214 = _addcarryx_u64(x211, x158, x194, &x213);
  { uint64_t x216; uint8_t x217 = _addcarryx_u64(x214, x161, x197, &x216);
  { uint64_t x219; uint8_t x220 = _addcarryx_u64(x217, x164, x200, &x219);
  { uint64_t x222; uint8_t x223 = _addcarryx_u64(x220, x167, x203, &x222);
  { uint64_t x225; uint8_t x226 = _addcarryx_u64(x223, x170, x205, &x225);
  { uint8_t x227 = (x226 + x171);
  { uint64_t x230;  uint64_t x229 = _mulx_u64(x9, x15, &x230);
  { uint64_t x233;  uint64_t x232 = _mulx_u64(x9, x17, &x233);
  { uint64_t x236;  uint64_t x235 = _mulx_u64(x9, x19, &x236);
  { uint64_t x239;  uint64_t x238 = _mulx_u64(x9, x21, &x239);
  { uint64_t x242;  uint64_t x241 = _mulx_u64(x9, x23, &x242);
  { uint64_t x245;  uint64_t x244 = _mulx_u64(x9, x22, &x245);
  { uint64_t x247; uint8_t x248 = _addcarryx_u64(0x0, x230, x232, &x247);
  { uint64_t x250; uint8_t x251 = _addcarryx_u64(x248, x233, x235, &x250);
  { uint64_t x253; uint8_t x254 = _addcarryx_u64(x251, x236, x238, &x253);
  { uint64_t x256; uint8_t x257 = _addcarryx_u64(x254, x239, x241, &x256);
  { uint64_t x259; uint8_t x260 = _addcarryx_u64(x257, x242, x244, &x259);
  { uint64_t x262; uint8_t _ = _addcarryx_u64(0x0, x260, x245, &x262);
  { uint64_t x265; uint8_t x266 = _addcarryx_u64(0x0, x210, x229, &x265);
  { uint64_t x268; uint8_t x269 = _addcarryx_u64(x266, x213, x247, &x268);
  { uint64_t x271; uint8_t x272 = _addcarryx_u64(x269, x216, x250, &x271);
  { uint64_t x274; uint8_t x275 = _addcarryx_u64(x272, x219, x253, &x274);
  { uint64_t x277; uint8_t x278 = _addcarryx_u64(x275, x222, x256, &x277);
  { uint64_t x280; uint8_t x281 = _addcarryx_u64(x278, x225, x259, &x280);
  { uint64_t x283; uint8_t x284 = _addcarryx_u64(x281, x227, x262, &x283);
  { uint64_t x287;  uint64_t x286 = _mulx_u64(x265, 0xffffffffffffffffL, &x287);
  { uint64_t x290;  uint64_t x289 = _mulx_u64(x265, 0xffffffffffffffffL, &x290);
  { uint64_t x293;  uint64_t x292 = _mulx_u64(x265, 0xfffffffdffffffffL, &x293);
  { uint64_t x296;  uint64_t x295 = _mulx_u64(x265, 0xffffffffffffffffL, &x296);
  { uint64_t x299;  uint64_t x298 = _mulx_u64(x265, 0xffffffffffffffffL, &x299);
  { uint8_t x302;  uint64_t x301 = _mulx_u64_out_u8(x265, 0x3, &x302);
  { uint64_t x304; uint8_t x305 = _addcarryx_u64(0x0, x287, x289, &x304);
  { uint64_t x307; uint8_t x308 = _addcarryx_u64(x305, x290, x292, &x307);
  { uint64_t x310; uint8_t x311 = _addcarryx_u64(x308, x293, x295, &x310);
  { uint64_t x313; uint8_t x314 = _addcarryx_u64(x311, x296, x298, &x313);
  { uint64_t x316; uint8_t x317 = _addcarryx_u64(x314, x299, x301, &x316);
  { uint8_t x318 = (x317 + x302);
  { uint64_t _; uint8_t x321 = _addcarryx_u64(0x0, x265, x286, &_);
  { uint64_t x323; uint8_t x324 = _addcarryx_u64(x321, x268, x304, &x323);
  { uint64_t x326; uint8_t x327 = _addcarryx_u64(x324, x271, x307, &x326);
  { uint64_t x329; uint8_t x330 = _addcarryx_u64(x327, x274, x310, &x329);
  { uint64_t x332; uint8_t x333 = _addcarryx_u64(x330, x277, x313, &x332);
  { uint64_t x335; uint8_t x336 = _addcarryx_u64(x333, x280, x316, &x335);
  { uint64_t x338; uint8_t x339 = _addcarryx_u64(x336, x283, x318, &x338);
  { uint8_t x340 = (x339 + x284);
  { uint64_t x343;  uint64_t x342 = _mulx_u64(x11, x15, &x343);
  { uint64_t x346;  uint64_t x345 = _mulx_u64(x11, x17, &x346);
  { uint64_t x349;  uint64_t x348 = _mulx_u64(x11, x19, &x349);
  { uint64_t x352;  uint64_t x351 = _mulx_u64(x11, x21, &x352);
  { uint64_t x355;  uint64_t x354 = _mulx_u64(x11, x23, &x355);
  { uint64_t x358;  uint64_t x357 = _mulx_u64(x11, x22, &x358);
  { uint64_t x360; uint8_t x361 = _addcarryx_u64(0x0, x343, x345, &x360);
  { uint64_t x363; uint8_t x364 = _addcarryx_u64(x361, x346, x348, &x363);
  { uint64_t x366; uint8_t x367 = _addcarryx_u64(x364, x349, x351, &x366);
  { uint64_t x369; uint8_t x370 = _addcarryx_u64(x367, x352, x354, &x369);
  { uint64_t x372; uint8_t x373 = _addcarryx_u64(x370, x355, x357, &x372);
  { uint64_t x375; uint8_t _ = _addcarryx_u64(0x0, x373, x358, &x375);
  { uint64_t x378; uint8_t x379 = _addcarryx_u64(0x0, x323, x342, &x378);
  { uint64_t x381; uint8_t x382 = _addcarryx_u64(x379, x326, x360, &x381);
  { uint64_t x384; uint8_t x385 = _addcarryx_u64(x382, x329, x363, &x384);
  { uint64_t x387; uint8_t x388 = _addcarryx_u64(x385, x332, x366, &x387);
  { uint64_t x390; uint8_t x391 = _addcarryx_u64(x388, x335, x369, &x390);
  { uint64_t x393; uint8_t x394 = _addcarryx_u64(x391, x338, x372, &x393);
  { uint64_t x396; uint8_t x397 = _addcarryx_u64(x394, x340, x375, &x396);
  { uint64_t x400;  uint64_t x399 = _mulx_u64(x378, 0xffffffffffffffffL, &x400);
  { uint64_t x403;  uint64_t x402 = _mulx_u64(x378, 0xffffffffffffffffL, &x403);
  { uint64_t x406;  uint64_t x405 = _mulx_u64(x378, 0xfffffffdffffffffL, &x406);
  { uint64_t x409;  uint64_t x408 = _mulx_u64(x378, 0xffffffffffffffffL, &x409);
  { uint64_t x412;  uint64_t x411 = _mulx_u64(x378, 0xffffffffffffffffL, &x412);
  { uint8_t x415;  uint64_t x414 = _mulx_u64_out_u8(x378, 0x3, &x415);
  { uint64_t x417; uint8_t x418 = _addcarryx_u64(0x0, x400, x402, &x417);
  { uint64_t x420; uint8_t x421 = _addcarryx_u64(x418, x403, x405, &x420);
  { uint64_t x423; uint8_t x424 = _addcarryx_u64(x421, x406, x408, &x423);
  { uint64_t x426; uint8_t x427 = _addcarryx_u64(x424, x409, x411, &x426);
  { uint64_t x429; uint8_t x430 = _addcarryx_u64(x427, x412, x414, &x429);
  { uint8_t x431 = (x430 + x415);
  { uint64_t _; uint8_t x434 = _addcarryx_u64(0x0, x378, x399, &_);
  { uint64_t x436; uint8_t x437 = _addcarryx_u64(x434, x381, x417, &x436);
  { uint64_t x439; uint8_t x440 = _addcarryx_u64(x437, x384, x420, &x439);
  { uint64_t x442; uint8_t x443 = _addcarryx_u64(x440, x387, x423, &x442);
  { uint64_t x445; uint8_t x446 = _addcarryx_u64(x443, x390, x426, &x445);
  { uint64_t x448; uint8_t x449 = _addcarryx_u64(x446, x393, x429, &x448);
  { uint64_t x451; uint8_t x452 = _addcarryx_u64(x449, x396, x431, &x451);
  { uint8_t x453 = (x452 + x397);
  { uint64_t x456;  uint64_t x455 = _mulx_u64(x13, x15, &x456);
  { uint64_t x459;  uint64_t x458 = _mulx_u64(x13, x17, &x459);
  { uint64_t x462;  uint64_t x461 = _mulx_u64(x13, x19, &x462);
  { uint64_t x465;  uint64_t x464 = _mulx_u64(x13, x21, &x465);
  { uint64_t x468;  uint64_t x467 = _mulx_u64(x13, x23, &x468);
  { uint64_t x471;  uint64_t x470 = _mulx_u64(x13, x22, &x471);
  { uint64_t x473; uint8_t x474 = _addcarryx_u64(0x0, x456, x458, &x473);
  { uint64_t x476; uint8_t x477 = _addcarryx_u64(x474, x459, x461, &x476);
  { uint64_t x479; uint8_t x480 = _addcarryx_u64(x477, x462, x464, &x479);
  { uint64_t x482; uint8_t x483 = _addcarryx_u64(x480, x465, x467, &x482);
  { uint64_t x485; uint8_t x486 = _addcarryx_u64(x483, x468, x470, &x485);
  { uint64_t x488; uint8_t _ = _addcarryx_u64(0x0, x486, x471, &x488);
  { uint64_t x491; uint8_t x492 = _addcarryx_u64(0x0, x436, x455, &x491);
  { uint64_t x494; uint8_t x495 = _addcarryx_u64(x492, x439, x473, &x494);
  { uint64_t x497; uint8_t x498 = _addcarryx_u64(x495, x442, x476, &x497);
  { uint64_t x500; uint8_t x501 = _addcarryx_u64(x498, x445, x479, &x500);
  { uint64_t x503; uint8_t x504 = _addcarryx_u64(x501, x448, x482, &x503);
  { uint64_t x506; uint8_t x507 = _addcarryx_u64(x504, x451, x485, &x506);
  { uint64_t x509; uint8_t x510 = _addcarryx_u64(x507, x453, x488, &x509);
  { uint64_t x513;  uint64_t x512 = _mulx_u64(x491, 0xffffffffffffffffL, &x513);
  { uint64_t x516;  uint64_t x515 = _mulx_u64(x491, 0xffffffffffffffffL, &x516);
  { uint64_t x519;  uint64_t x518 = _mulx_u64(x491, 0xfffffffdffffffffL, &x519);
  { uint64_t x522;  uint64_t x521 = _mulx_u64(x491, 0xffffffffffffffffL, &x522);
  { uint64_t x525;  uint64_t x524 = _mulx_u64(x491, 0xffffffffffffffffL, &x525);
  { uint8_t x528;  uint64_t x527 = _mulx_u64_out_u8(x491, 0x3, &x528);
  { uint64_t x530; uint8_t x531 = _addcarryx_u64(0x0, x513, x515, &x530);
  { uint64_t x533; uint8_t x534 = _addcarryx_u64(x531, x516, x518, &x533);
  { uint64_t x536; uint8_t x537 = _addcarryx_u64(x534, x519, x521, &x536);
  { uint64_t x539; uint8_t x540 = _addcarryx_u64(x537, x522, x524, &x539);
  { uint64_t x542; uint8_t x543 = _addcarryx_u64(x540, x525, x527, &x542);
  { uint8_t x544 = (x543 + x528);
  { uint64_t _; uint8_t x547 = _addcarryx_u64(0x0, x491, x512, &_);
  { uint64_t x549; uint8_t x550 = _addcarryx_u64(x547, x494, x530, &x549);
  { uint64_t x552; uint8_t x553 = _addcarryx_u64(x550, x497, x533, &x552);
  { uint64_t x555; uint8_t x556 = _addcarryx_u64(x553, x500, x536, &x555);
  { uint64_t x558; uint8_t x559 = _addcarryx_u64(x556, x503, x539, &x558);
  { uint64_t x561; uint8_t x562 = _addcarryx_u64(x559, x506, x542, &x561);
  { uint64_t x564; uint8_t x565 = _addcarryx_u64(x562, x509, x544, &x564);
  { uint8_t x566 = (x565 + x510);
  { uint64_t x569;  uint64_t x568 = _mulx_u64(x12, x15, &x569);
  { uint64_t x572;  uint64_t x571 = _mulx_u64(x12, x17, &x572);
  { uint64_t x575;  uint64_t x574 = _mulx_u64(x12, x19, &x575);
  { uint64_t x578;  uint64_t x577 = _mulx_u64(x12, x21, &x578);
  { uint64_t x581;  uint64_t x580 = _mulx_u64(x12, x23, &x581);
  { uint64_t x584;  uint64_t x583 = _mulx_u64(x12, x22, &x584);
  { uint64_t x586; uint8_t x587 = _addcarryx_u64(0x0, x569, x571, &x586);
  { uint64_t x589; uint8_t x590 = _addcarryx_u64(x587, x572, x574, &x589);
  { uint64_t x592; uint8_t x593 = _addcarryx_u64(x590, x575, x577, &x592);
  { uint64_t x595; uint8_t x596 = _addcarryx_u64(x593, x578, x580, &x595);
  { uint64_t x598; uint8_t x599 = _addcarryx_u64(x596, x581, x583, &x598);
  { uint64_t x601; uint8_t _ = _addcarryx_u64(0x0, x599, x584, &x601);
  { uint64_t x604; uint8_t x605 = _addcarryx_u64(0x0, x549, x568, &x604);
  { uint64_t x607; uint8_t x608 = _addcarryx_u64(x605, x552, x586, &x607);
  { uint64_t x610; uint8_t x611 = _addcarryx_u64(x608, x555, x589, &x610);
  { uint64_t x613; uint8_t x614 = _addcarryx_u64(x611, x558, x592, &x613);
  { uint64_t x616; uint8_t x617 = _addcarryx_u64(x614, x561, x595, &x616);
  { uint64_t x619; uint8_t x620 = _addcarryx_u64(x617, x564, x598, &x619);
  { uint64_t x622; uint8_t x623 = _addcarryx_u64(x620, x566, x601, &x622);
  { uint64_t x626;  uint64_t x625 = _mulx_u64(x604, 0xffffffffffffffffL, &x626);
  { uint64_t x629;  uint64_t x628 = _mulx_u64(x604, 0xffffffffffffffffL, &x629);
  { uint64_t x632;  uint64_t x631 = _mulx_u64(x604, 0xfffffffdffffffffL, &x632);
  { uint64_t x635;  uint64_t x634 = _mulx_u64(x604, 0xffffffffffffffffL, &x635);
  { uint64_t x638;  uint64_t x637 = _mulx_u64(x604, 0xffffffffffffffffL, &x638);
  { uint8_t x641;  uint64_t x640 = _mulx_u64_out_u8(x604, 0x3, &x641);
  { uint64_t x643; uint8_t x644 = _addcarryx_u64(0x0, x626, x628, &x643);
  { uint64_t x646; uint8_t x647 = _addcarryx_u64(x644, x629, x631, &x646);
  { uint64_t x649; uint8_t x650 = _addcarryx_u64(x647, x632, x634, &x649);
  { uint64_t x652; uint8_t x653 = _addcarryx_u64(x650, x635, x637, &x652);
  { uint64_t x655; uint8_t x656 = _addcarryx_u64(x653, x638, x640, &x655);
  { uint8_t x657 = (x656 + x641);
  { uint64_t _; uint8_t x660 = _addcarryx_u64(0x0, x604, x625, &_);
  { uint64_t x662; uint8_t x663 = _addcarryx_u64(x660, x607, x643, &x662);
  { uint64_t x665; uint8_t x666 = _addcarryx_u64(x663, x610, x646, &x665);
  { uint64_t x668; uint8_t x669 = _addcarryx_u64(x666, x613, x649, &x668);
  { uint64_t x671; uint8_t x672 = _addcarryx_u64(x669, x616, x652, &x671);
  { uint64_t x674; uint8_t x675 = _addcarryx_u64(x672, x619, x655, &x674);
  { uint64_t x677; uint8_t x678 = _addcarryx_u64(x675, x622, x657, &x677);
  { uint8_t x679 = (x678 + x623);
  { uint64_t x681; uint8_t x682 = _subborrow_u64(0x0, x662, 0xffffffffffffffffL, &x681);
  { uint64_t x684; uint8_t x685 = _subborrow_u64(x682, x665, 0xffffffffffffffffL, &x684);
  { uint64_t x687; uint8_t x688 = _subborrow_u64(x685, x668, 0xfffffffdffffffffL, &x687);
  { uint64_t x690; uint8_t x691 = _subborrow_u64(x688, x671, 0xffffffffffffffffL, &x690);
  { uint64_t x693; uint8_t x694 = _subborrow_u64(x691, x674, 0xffffffffffffffffL, &x693);
  { uint64_t x696; uint8_t x697 = _subborrow_u64(x694, x677, 0x3, &x696);
  { uint64_t _; uint8_t x700 = _subborrow_u64(x697, x679, 0x0, &_);
  { uint64_t x701 = cmovznz64(x700, x696, x677);
  { uint64_t x702 = cmovznz64(x700, x693, x674);
  { uint64_t x703 = cmovznz64(x700, x690, x671);
  { uint64_t x704 = cmovznz64(x700, x687, x668);
  { uint64_t x705 = cmovznz64(x700, x684, x665);
  { uint64_t x706 = cmovznz64(x700, x681, x662);
  out[0] = x706;
  out[1] = x705;
  out[2] = x704;
  out[3] = x703;
  out[4] = x702;
  out[5] = x701;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}
