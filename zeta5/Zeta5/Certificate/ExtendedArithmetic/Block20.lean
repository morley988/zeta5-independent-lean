import Zeta5.Certificate.ExtendedArithmetic.Core

namespace Zeta5.Certificate.ExtendedArithmetic

namespace Block20

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def cells : List (ArithmeticCell × ℚ) := [
  (⟨(532 / 45475), (5 / 426), 85, false, 213, false⟩, (108371521 / 500000000000)),
  (⟨(5 / 426), (1 / 85), 85, false, 212, false⟩, (139464237 / 1000000000000)),
  (⟨(1 / 85), (706 / 59995), 84, true, 212, true⟩, (5294559 / 250000000000)),
  (⟨(706 / 59995), (5 / 424), 84, true, 212, false⟩, (21632803 / 125000000000)),
  (⟨(5 / 424), (2 / 169), 84, true, 211, false⟩, (26690019 / 100000000000)),
  (⟨(2 / 169), (527 / 44520), 84, false, 211, true⟩, (18341601 / 1000000000000)),
  (⟨(527 / 44520), (5 / 422), 84, false, 211, false⟩, (64718139 / 1000000000000)),
  (⟨(5 / 422), (1 / 84), 84, false, 210, false⟩, (59805913 / 200000000000)),
  (⟨(1 / 84), (348 / 29225), 83, true, 209, true⟩, (320787 / 15625000000)),
  (⟨(348 / 29225), (5 / 418), 83, true, 209, false⟩, (363916351 / 1000000000000)),
  (⟨(5 / 418), (2 / 167), 83, true, 208, false⟩, (43871587 / 500000000000)),
  (⟨(2 / 167), (1039 / 86735), 83, false, 208, true⟩, (17811843 / 1000000000000)),
  (⟨(1039 / 86735), (5 / 416), 83, false, 208, false⟩, (14203669 / 62500000000)),
  (⟨(5 / 416), (1 / 83), 83, false, 207, false⟩, (14625811 / 100000000000)),
  (⟨(1 / 83), (47 / 3900), 82, true, 207, true⟩, (11121409 / 500000000000)),
  (⟨(47 / 3900), (5 / 414), 82, true, 207, false⟩, (45371313 / 250000000000)),
  (⟨(5 / 414), (2 / 165), 82, true, 206, false⟩, (5599473 / 20000000000)),
  (⟨(2 / 165), (343 / 28290), 82, false, 206, true⟩, (9640413 / 500000000000)),
  (⟨(343 / 28290), (5 / 412), 82, false, 206, false⟩, (67858659 / 1000000000000)),
  (⟨(5 / 412), (1 / 82), 82, false, 205, false⟩, (39219749 / 125000000000)),
  (⟨(1 / 82), (2038 / 167075), 81, true, 204, true⟩, (2154721 / 100000000000)),
  (⟨(2038 / 167075), (5 / 408), 81, true, 204, false⟩, (381929669 / 1000000000000)),
  (⟨(5 / 408), (2 / 163), 81, true, 203, false⟩, (23024931 / 250000000000)),
  (⟨(2 / 163), (169 / 13770), 81, false, 203, true⟩, (748493 / 40000000000)),
  (⟨(169 / 13770), (5 / 406), 81, false, 203, false⟩, (238558629 / 1000000000000)),
  (⟨(5 / 406), (1 / 81), 81, false, 202, false⟩, (76780393 / 500000000000)),
  (⟨(1 / 81), (2018 / 163415), 80, true, 202, true⟩, (11694833 / 500000000000)),
  (⟨(2018 / 163415), (5 / 404), 80, true, 202, false⟩, (47634569 / 250000000000)),
  (⟨(5 / 404), (2 / 161), 80, true, 201, false⟩, (294031733 / 1000000000000)),
  (⟨(2 / 161), (251 / 20200), 80, false, 201, true⟩, (4058791 / 200000000000)),
  (⟨(251 / 20200), (5 / 402), 80, false, 201, false⟩, (7123341 / 100000000000)),
  (⟨(5 / 402), (1 / 80), 80, false, 200, false⟩, (329601991 / 1000000000000)),
  (⟨(1 / 80), (497 / 39750), 79, true, 199, true⟩, (2264151 / 100000000000)),
  (⟨(497 / 39750), (5 / 398), 79, true, 199, false⟩, (200657153 / 500000000000)),
  (⟨(5 / 398), (2 / 159), 79, true, 198, false⟩, (96788977 / 1000000000000)),
  (⟨(2 / 159), (989 / 78605), 79, false, 198, true⟩, (19682843 / 1000000000000)),
  (⟨(989 / 78605), (5 / 396), 79, false, 198, false⟩, (25072279 / 100000000000)),
  (⟨(5 / 396), (1 / 79), 79, false, 197, false⟩, (161424371 / 1000000000000)),
  (⟨(1 / 79), (328 / 25905), 78, true, 197, true⟩, (24627473 / 1000000000000)),
  (⟨(328 / 25905), (5 / 394), 78, true, 197, false⟩, (200285967 / 1000000000000)),
  (⟨(5 / 394), (2 / 157), 78, true, 196, false⟩, (61835171 / 200000000000)),
  (⟨(2 / 157), (979 / 76830), 78, false, 196, true⟩, (10694469 / 500000000000)),
  (⟨(979 / 76830), (5 / 392), 78, false, 196, false⟩, (74866273 / 1000000000000)),
  (⟨(5 / 392), (1 / 78), 78, false, 195, false⟩, (346677133 / 1000000000000)),
  (⟨(1 / 78), (646 / 50375), 77, true, 194, true⟩, (1191067 / 50000000000)),
  (⟨(646 / 50375), (5 / 388), 77, true, 194, false⟩, (26388317 / 62500000000)),
  (⟨(5 / 388), (2 / 155), 77, true, 193, false⟩, (50922847 / 500000000000)),
  (⟨(2 / 155), (482 / 37345), 77, false, 193, true⟩, (20730849 / 1000000000000)),
  (⟨(482 / 37345), (5 / 386), 77, false, 193, false⟩, (263841617 / 1000000000000)),
  (⟨(5 / 386), (1 / 77), 77, false, 192, false⟩, (169907813 / 1000000000000)),
  (⟨(1 / 77), (1918 / 147645), 76, true, 192, true⟩, (2596611 / 100000000000)),
  (⟨(1918 / 147645), (5 / 384), 76, true, 192, false⟩, (210801259 / 1000000000000)),
  (⟨(5 / 384), (2 / 153), 76, true, 191, false⟩, (162760417 / 500000000000)),
  (⟨(2 / 153), (159 / 12160), 76, false, 191, true⟩, (1128741 / 50000000000)),
  (⟨(159 / 12160), (5 / 382), 76, false, 191, false⟩, (19696063 / 250000000000)),
  (⟨(5 / 382), (1 / 76), 76, false, 190, false⟩, (365114357 / 1000000000000)),
  (⟨(1 / 76), (944 / 71725), 75, true, 189, true⟩, (25095853 / 1000000000000)),
  (⟨(944 / 71725), (5 / 378), 75, true, 189, false⟩, (222393933 / 500000000000)),
  (⟨(5 / 378), (2 / 151), 75, true, 188, false⟩, (107309297 / 1000000000000)),
  (⟨(2 / 151), (313 / 23625), 75, false, 188, true⟩, (21864817 / 1000000000000)),
  (⟨(313 / 23625), (5 / 376), 75, false, 188, false⟩, (34752211 / 125000000000)),
  (⟨(5 / 376), (1 / 75), 75, false, 187, false⟩, (35815603 / 200000000000)),
  (⟨(1 / 75), (467 / 35015), 74, true, 187, true⟩, (13708411 / 500000000000)),
  (⟨(467 / 35015), (5 / 374), 74, true, 187, false⟩, (1735679 / 7812500000)),
  (⟨(5 / 374), (2 / 149), 74, true, 186, false⟩, (21449817 / 62500000000)),
  (⟨(2 / 149), (929 / 69190), 74, false, 186, true⟩, (23861927 / 1000000000000)),
  (⟨(929 / 69190), (5 / 372), 74, false, 186, false⟩, (10377247 / 125000000000)),
  (⟨(5 / 372), (1 / 74), 74, false, 185, false⟩, (192531241 / 500000000000)),
  (⟨(1 / 74), (1838 / 135975), 73, true, 184, true⟩, (413679 / 15625000000)),
  (⟨(1838 / 135975), (5 / 368), 73, true, 184, false⟩, (14663213 / 31250000000)),
  (⟨(5 / 368), (2 / 147), 73, true, 183, false⟩, (56612319 / 500000000000)),
  (⟨(2 / 147), (457 / 33580), 73, false, 183, true⟩, (2886801 / 125000000000)),
  (⟨(457 / 33580), (5 / 366), 73, false, 183, false⟩, (146683867 / 500000000000)),
  (⟨(5 / 366), (1 / 73), 73, false, 182, false⟩, (94505577 / 500000000000)),
  (⟨(1 / 73), (606 / 44225), 72, true, 182, true⟩, (14496233 / 500000000000)),
  (⟨(606 / 44225), (5 / 364), 72, true, 182, false⟩, (4689543 / 20000000000)),
  (⟨(5 / 364), (2 / 145), 72, true, 181, false⟩, (72470633 / 200000000000)),
  (⟨(2 / 145), (113 / 8190), 72, false, 181, true⟩, (5052419 / 200000000000)),
  (⟨(113 / 8190), (5 / 362), 72, false, 181, false⟩, (876023 / 10000000000)),
  (⟨(5 / 362), (1 / 72), 72, false, 180, false⟩, (203345611 / 500000000000)),
  (⟨(1 / 72), (149 / 10725), 71, true, 179, true⟩, (6993007 / 250000000000)),
  (⟨(149 / 10725), (5 / 358), 71, true, 179, false⟩, (30983003 / 62500000000)),
  (⟨(5 / 358), (2 / 143), 71, true, 178, false⟩, (119642927 / 1000000000000)),
  (⟨(2 / 143), (889 / 63545), 71, false, 178, true⟩, (610767 / 25000000000)),
  (⟨(889 / 63545), (5 / 356), 71, false, 178, false⟩, (62005011 / 200000000000)),
  (⟨(5 / 356), (1 / 71), 71, false, 177, false⟩, (6243571 / 31250000000)),
  (⟨(1 / 71), (884 / 62745), 70, true, 177, true⟩, (6141559 / 200000000000)),
  (⟨(884 / 62745), (5 / 354), 70, true, 177, false⟩, (49567923 / 200000000000)),
  (⟨(5 / 354), (2 / 141), 70, true, 176, false⟩, (191579517 / 500000000000)),
  (⟨(2 / 141), (293 / 20650), 70, false, 176, true⟩, (5357787 / 200000000000)),
  (⟨(293 / 20650), (5 / 352), 70, false, 176, false⟩, (92577023 / 1000000000000)),
  (⟨(5 / 352), (1 / 70), 70, false, 175, false⟩, (215097403 / 500000000000)),
  (⟨(1 / 70), (1738 / 121625), 69, true, 174, true⟩, (14799589 / 500000000000)),
  (⟨(1738 / 121625), (5 / 348), 69, true, 174, false⟩, (524544221 / 1000000000000)),
  (⟨(5 / 348), (2 / 139), 69, true, 173, false⟩, (3165571 / 25000000000)),
  (⟨(2 / 139), (48 / 3335), 69, false, 173, true⟩, (12943169 / 500000000000)),
  (⟨(48 / 3335), (5 / 346), 69, false, 173, false⟩, (328142421 / 1000000000000)),
  (⟨(5 / 346), (1 / 69), 69, false, 172, false⟩, (42305437 / 200000000000)),
  (⟨(1 / 69), (1718 / 118505), 68, true, 172, true⟩, (8144951 / 250000000000)),
  (⟨(1718 / 118505), (5 / 344), 68, true, 172, false⟩, (32797217 / 125000000000)),
  (⟨(5 / 344), (2 / 137), 68, true, 171, false⟩, (40580971 / 100000000000)),
  (⟨(2 / 137), (427 / 29240), 68, false, 171, true⟩, (28458167 / 1000000000000)),
  (⟨(427 / 29240), (5 / 342), 68, false, 171, false⟩, (19597551 / 200000000000)),
  (⟨(5 / 342), (1 / 68), 68, false, 170, false⟩, (227898177 / 500000000000)),
  (⟨(1 / 68), (844 / 57375), 67, true, 169, true⟩, (627451 / 20000000000)),
  (⟨(844 / 57375), (5 / 338), 67, true, 169, false⟩, (138987001 / 250000000000)),
  (⟨(5 / 338), (2 / 135), 67, true, 168, false⟩, (67115933 / 500000000000)),
  (⟨(2 / 135), (839 / 56615), 67, false, 168, true⟩, (27476033 / 1000000000000)),
  (⟨(839 / 56615), (5 / 336), 67, false, 168, false⟩, (34789559 / 100000000000)),
  (⟨(5 / 336), (1 / 67), 67, false, 167, false⟩, (44864961 / 200000000000)),
  (⟨(1 / 67), (139 / 9310), 66, true, 167, true⟩, (34628149 / 1000000000000)),
  (⟨(139 / 9310), (5 / 334), 66, true, 167, false⟩, (278233579 / 1000000000000)),
  (⟨(5 / 334), (2 / 133), 66, true, 166, false⟩, (215264959 / 500000000000)),
  (⟨(2 / 133), (829 / 55110), 66, false, 166, true⟩, (30288023 / 1000000000000)),
  (⟨(829 / 55110), (5 / 332), 66, false, 166, false⟩, (103886963 / 1000000000000)),
  (⟨(5 / 332), (1 / 66), 66, false, 165, false⟩, (96750639 / 200000000000)),
  (⟨(1 / 66), (546 / 36025), 65, true, 164, true⟩, (16655101 / 500000000000)),
  (⟨(546 / 36025), (5 / 328), 65, true, 164, false⟩, (590258747 / 1000000000000)),
  (⟨(5 / 328), (2 / 131), 65, true, 163, false⟩, (142547943 / 1000000000000)),
  (⟨(2 / 131), (407 / 26650), 65, false, 163, true⟩, (14608367 / 500000000000)),
  (⟨(407 / 26650), (5 / 326), 65, false, 163, false⟩, (369487583 / 1000000000000)),
  (⟨(5 / 326), (1 / 65), 65, false, 162, false⟩, (238319963 / 1000000000000)),
  (⟨(1 / 65), (1618 / 105135), 64, true, 162, true⟩, (18437833 / 500000000000)),
  (⟨(1618 / 105135), (5 / 324), 64, true, 162, false⟩, (295571341 / 1000000000000)),
  (⟨(5 / 324), (2 / 129), 64, true, 161, false⟩, (457579673 / 1000000000000)),
  (⟨(2 / 129), (67 / 4320), 64, false, 161, true⟩, (16149871 / 500000000000)),
  (⟨(67 / 4320), (5 / 322), 64, false, 161, false⟩, (441341 / 4000000000)),
  (⟨(5 / 322), (1 / 64), 64, false, 160, false⟩, (102872671 / 200000000000))]

theorem fits : cappedChainFits (532 / 45475) cells := by
  unfold cells
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]
  trivial

theorem endpoint : cappedChainEnd (532 / 45475) cells = (1 / 64) := by rfl

theorem upper : cappedChainUpper cells = (1179767457 / 50000000000) := by
  norm_num [cappedChainUpper, cells]

theorem bound :
    IntervalIntegrable middleRankProfile MeasureTheory.volume ((532 / 45475) : ℝ) ((1 / 64) : ℝ) ∧
    (∫ β in ((532 / 45475) : ℝ)..((1 / 64) : ℝ), middleRankProfile β) ≤ ((1179767457 / 50000000000) : ℝ) := by
  have h := integrate_cappedChain fits
  rw [endpoint, upper] at h
  norm_num at h ⊢
  exact h

end Block20
end Zeta5.Certificate.ExtendedArithmetic
