import Zeta5.Certificate.ExtendedArithmetic.Core

namespace Zeta5.Certificate.ExtendedArithmetic

namespace Block16

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def cells : List (ArithmeticCell × ℚ) := [
  (⟨(5 / 854), (2 / 341), 170, true, 426, false⟩, (32836677 / 500000000000)),
  (⟨(2 / 341), (2129 / 362950), 170, false, 426, true⟩, (1078649 / 250000000000)),
  (⟨(2129 / 362950), (5 / 852), 170, false, 426, false⟩, (3213617 / 200000000000)),
  (⟨(5 / 852), (1 / 170), 170, false, 425, false⟩, (18296051 / 250000000000)),
  (⟨(1 / 170), (4238 / 720375), 169, true, 424, true⟩, (2498699 / 500000000000)),
  (⟨(4238 / 720375), (5 / 848), 169, true, 424, false⟩, (8863529 / 100000000000)),
  (⟨(5 / 848), (2 / 339), 169, true, 423, false⟩, (21306423 / 1000000000000)),
  (⟨(2 / 339), (1057 / 179140), 169, false, 423, true⟩, (212421 / 50000000000)),
  (⟨(1057 / 179140), (5 / 846), 169, false, 423, false⟩, (6888353 / 125000000000)),
  (⟨(5 / 846), (1 / 169), 169, false, 422, false⟩, (8830277 / 250000000000)),
  (⟨(1 / 169), (1406 / 237585), 168, true, 422, true⟩, (5200257 / 1000000000000)),
  (⟨(1406 / 237585), (5 / 844), 168, true, 422, false⟩, (21934269 / 500000000000)),
  (⟨(5 / 844), (2 / 337), 168, true, 421, false⟩, (8405027 / 125000000000)),
  (⟨(2 / 337), (263 / 44310), 168, false, 421, true⟩, (4419899 / 1000000000000)),
  (⟨(263 / 44310), (5 / 842), 168, false, 421, false⟩, (2056217 / 125000000000)),
  (⟨(5 / 842), (1 / 168), 168, false, 420, false⟩, (74934963 / 1000000000000)),
  (⟨(1 / 168), (349 / 58625), 167, true, 419, true⟩, (5117271 / 1000000000000)),
  (⟨(349 / 58625), (5 / 838), 167, true, 419, false⟩, (45380389 / 500000000000)),
  (⟨(5 / 838), (2 / 335), 167, true, 418, false⟩, (10909059 / 500000000000)),
  (⟨(2 / 335), (2089 / 349865), 167, false, 418, true⟩, (4351359 / 1000000000000)),
  (⟨(2089 / 349865), (5 / 836), 167, false, 418, false⟩, (56431189 / 1000000000000)),
  (⟨(5 / 836), (1 / 167), 167, false, 417, false⟩, (9042919 / 250000000000)),
  (⟨(1 / 167), (2084 / 347985), 166, true, 417, true⟩, (5327507 / 1000000000000)),
  (⟨(2084 / 347985), (5 / 834), 166, true, 417, false⟩, (44924467 / 1000000000000)),
  (⟨(5 / 834), (2 / 333), 166, true, 416, false⟩, (17215957 / 250000000000)),
  (⟨(2 / 333), (693 / 115370), 166, false, 416, true⟩, (4529103 / 1000000000000)),
  (⟨(693 / 115370), (5 / 832), 166, false, 416, false⟩, (4211287 / 250000000000)),
  (⟨(5 / 832), (1 / 166), 166, false, 415, false⟩, (15349861 / 200000000000)),
  (⟨(1 / 166), (4138 / 686825), 165, true, 414, true⟩, (524151 / 100000000000)),
  (⟨(4138 / 686825), (5 / 828), 165, true, 414, false⟩, (92963647 / 1000000000000)),
  (⟨(5 / 828), (2 / 331), 165, true, 413, false⟩, (22348469 / 1000000000000)),
  (⟨(2 / 331), (344 / 56925), 165, false, 413, true⟩, (891617 / 200000000000)),
  (⟨(344 / 56925), (5 / 826), 165, false, 413, false⟩, (57803877 / 1000000000000)),
  (⟨(5 / 826), (1 / 165), 165, false, 412, false⟩, (37053343 / 1000000000000)),
  (⟨(1 / 165), (4118 / 679385), 164, true, 412, true⟩, (1364871 / 250000000000)),
  (⟨(4118 / 679385), (5 / 824), 164, true, 412, false⟩, (5752373 / 125000000000)),
  (⟨(5 / 824), (2 / 329), 164, true, 411, false⟩, (14109393 / 200000000000)),
  (⟨(2 / 329), (1027 / 168920), 164, false, 411, true⟩, (2321201 / 500000000000)),
  (⟨(1027 / 168920), (5 / 822), 164, false, 411, false⟩, (1725499 / 100000000000)),
  (⟨(5 / 822), (1 / 164), 164, false, 410, false⟩, (78630349 / 1000000000000)),
  (⟨(1 / 164), (2044 / 335175), 163, true, 409, true⟩, (5370329 / 1000000000000)),
  (⟨(2044 / 335175), (5 / 818), 163, true, 409, false⟩, (952477 / 10000000000)),
  (⟨(5 / 818), (2 / 327), 163, true, 408, false⟩, (4579679 / 200000000000)),
  (⟨(2 / 327), (2039 / 333335), 163, false, 408, true⟩, (913757 / 200000000000)),
  (⟨(2039 / 333335), (5 / 816), 163, false, 408, false⟩, (59227267 / 1000000000000)),
  (⟨(5 / 816), (1 / 163), 163, false, 407, false⟩, (18983821 / 500000000000)),
  (⟨(1 / 163), (339 / 55250), 162, true, 407, true⟩, (223857 / 40000000000)),
  (⟨(339 / 55250), (5 / 814), 162, true, 407, false⟩, (47153993 / 1000000000000)),
  (⟨(5 / 814), (2 / 325), 162, true, 406, false⟩, (72292573 / 1000000000000)),
  (⟨(2 / 325), (2029 / 329670), 162, false, 406, true⟩, (952001 / 200000000000)),
  (⟨(2029 / 329670), (5 / 812), 162, false, 406, false⟩, (4419993 / 250000000000)),
  (⟨(5 / 812), (1 / 162), 162, false, 405, false⟩, (80581403 / 1000000000000)),
  (⟨(1 / 162), (1346 / 218025), 161, true, 404, true⟩, (1375989 / 250000000000)),
  (⟨(1346 / 218025), (5 / 808), 161, true, 404, false⟩, (3904679 / 40000000000)),
  (⟨(5 / 808), (2 / 323), 161, true, 403, false⟩, (2933609 / 125000000000)),
  (⟨(2 / 323), (1007 / 162610), 161, false, 403, true⟩, (234183 / 50000000000)),
  (⟨(1007 / 162610), (5 / 806), 161, false, 403, false⟩, (30351943 / 500000000000)),
  (⟨(5 / 806), (1 / 161), 161, false, 402, false⟩, (9729051 / 250000000000)),
  (⟨(1 / 161), (4018 / 646815), 160, true, 402, true⟩, (5738583 / 1000000000000)),
  (⟨(4018 / 646815), (5 / 804), 160, true, 402, false⟩, (48331517 / 1000000000000)),
  (⟨(5 / 804), (2 / 321), 160, true, 401, false⟩, (74103781 / 1000000000000)),
  (⟨(2 / 321), (167 / 26800), 160, false, 401, true⟩, (1220533 / 250000000000)),
  (⟨(167 / 26800), (5 / 802), 160, false, 401, false⟩, (362417 / 20000000000)),
  (⟨(5 / 802), (1 / 160), 160, false, 400, false⟩, (41302993 / 500000000000)),
  (⟨(1 / 160), (997 / 159500), 159, true, 399, true⟩, (2821317 / 500000000000)),
  (⟨(997 / 159500), (5 / 798), 159, true, 399, false⟩, (20015153 / 200000000000)),
  (⟨(5 / 798), (2 / 319), 159, true, 398, false⟩, (24060937 / 1000000000000)),
  (⟨(2 / 319), (221 / 35245), 159, false, 398, true⟩, (4802923 / 1000000000000)),
  (⟨(221 / 35245), (5 / 796), 159, false, 398, false⟩, (7779553 / 125000000000)),
  (⟨(5 / 796), (1 / 159), 159, false, 397, false⟩, (19950381 / 500000000000)),
  (⟨(1 / 159), (1984 / 315415), 158, true, 397, true⟩, (2943113 / 500000000000)),
  (⟨(1984 / 315415), (5 / 794), 158, true, 397, false⟩, (9910741 / 200000000000)),
  (⟨(5 / 794), (2 / 317), 158, true, 396, false⟩, (37991959 / 500000000000)),
  (⟨(2 / 317), (1979 / 313630), 158, false, 396, true⟩, (5009017 / 1000000000000)),
  (⟨(1979 / 313630), (5 / 792), 158, false, 396, false⟩, (9289213 / 500000000000)),
  (⟨(5 / 792), (1 / 158), 158, false, 395, false⟩, (42353919 / 500000000000)),
  (⟨(1 / 158), (3938 / 622125), 157, true, 394, true⟩, (5786619 / 1000000000000)),
  (⟨(3938 / 622125), (5 / 788), 157, true, 394, false⟩, (102628637 / 1000000000000)),
  (⟨(5 / 788), (2 / 315), 157, true, 393, false⟩, (24675691 / 1000000000000)),
  (⟨(2 / 315), (982 / 154645), 157, false, 393, true⟩, (4926799 / 1000000000000)),
  (⟨(982 / 154645), (5 / 786), 157, false, 393, false⟩, (31913869 / 500000000000)),
  (⟨(5 / 786), (1 / 157), 157, false, 392, false⟩, (20461581 / 500000000000)),
  (⟨(1 / 157), (1306 / 205015), 156, true, 392, true⟩, (6039639 / 1000000000000)),
  (⟨(1306 / 205015), (5 / 784), 156, true, 392, false⟩, (10164569 / 200000000000)),
  (⟨(5 / 784), (2 / 313), 156, true, 391, false⟩, (77936527 / 1000000000000)),
  (⟨(2 / 313), (977 / 152880), 156, false, 391, true⟩, (321307 / 62500000000)),
  (⟨(977 / 152880), (5 / 782), 156, false, 391, false⟩, (3810711 / 200000000000)),
  (⟨(5 / 782), (1 / 156), 156, false, 390, false⟩, (1357671 / 15625000000)),
  (⟨(1 / 156), (648 / 101075), 155, true, 389, true⟩, (5936187 / 1000000000000)),
  (⟨(648 / 101075), (5 / 778), 155, true, 389, false⟩, (52640227 / 500000000000)),
  (⟨(5 / 778), (2 / 311), 155, true, 388, false⟩, (25314311 / 1000000000000)),
  (⟨(2 / 311), (1939 / 301475), 155, false, 388, true⟩, (505553 / 100000000000)),
  (⟨(1939 / 301475), (5 / 776), 155, false, 388, false⟩, (32740437 / 500000000000)),
  (⟨(5 / 776), (1 / 155), 155, false, 387, false⟩, (5248171 / 125000000000)),
  (⟨(1 / 155), (967 / 149865), 154, true, 387, true⟩, (774891 / 125000000000)),
  (⟨(967 / 149865), (5 / 774), 154, true, 387, false⟩, (52141373 / 1000000000000)),
  (⟨(5 / 774), (2 / 309), 154, true, 386, false⟩, (3998269 / 50000000000)),
  (⟨(2 / 309), (643 / 99330), 154, false, 386, true⟩, (2639041 / 500000000000)),
  (⟨(643 / 99330), (5 / 772), 154, false, 386, false⟩, (3909429 / 200000000000)),
  (⟨(5 / 772), (1 / 154), 154, false, 385, false⟩, (44579773 / 500000000000)),
  (⟨(1 / 154), (3838 / 590975), 153, true, 384, true⟩, (6091629 / 1000000000000)),
  (⟨(3838 / 590975), (5 / 768), 153, true, 384, false⟩, (54018197 / 500000000000)),
  (⟨(5 / 768), (2 / 307), 153, true, 383, false⟩, (25978047 / 1000000000000)),
  (⟨(2 / 307), (319 / 48960), 153, false, 383, true⟩, (5189373 / 1000000000000)),
  (⟨(319 / 48960), (5 / 766), 153, false, 383, false⟩, (16799769 / 250000000000)),
  (⟨(5 / 766), (1 / 153), 153, false, 382, false⟩, (43089473 / 1000000000000)),
  (⟨(1 / 153), (3818 / 584075), 152, true, 382, true⟩, (6365017 / 1000000000000)),
  (⟨(3818 / 584075), (5 / 764), 152, true, 382, false⟩, (26755943 / 500000000000)),
  (⟨(5 / 764), (2 / 305), 152, true, 381, false⟩, (82074501 / 1000000000000)),
  (⟨(2 / 305), (119 / 18145), 152, false, 381, true⟩, (2710407 / 500000000000)),
  (⟨(119 / 18145), (5 / 762), 152, false, 381, false⟩, (10030083 / 500000000000)),
  (⟨(5 / 762), (1 / 152), 152, false, 380, false⟩, (45759083 / 500000000000)),
  (⟨(1 / 152), (947 / 143925), 151, true, 379, true⟩, (6253257 / 1000000000000)),
  (⟨(947 / 143925), (5 / 758), 151, true, 379, false⟩, (55450991 / 500000000000)),
  (⟨(5 / 758), (2 / 303), 151, true, 378, false⟩, (5333647 / 200000000000)),
  (⟨(2 / 303), (1889 / 286145), 151, false, 378, true⟩, (5328601 / 1000000000000)),
  (⟨(1889 / 286145), (5 / 756), 151, false, 378, false⟩, (17246451 / 250000000000)),
  (⟨(5 / 756), (1 / 151), 151, false, 377, false⟩, (4423771 / 100000000000)),
  (⟨(1 / 151), (628 / 94815), 150, true, 377, true⟩, (6537653 / 1000000000000)),
  (⟨(628 / 94815), (5 / 754), 150, true, 377, false⟩, (858393 / 15625000000)),
  (⟨(5 / 754), (2 / 301), 150, true, 376, false⟩, (42134089 / 500000000000)),
  (⟨(2 / 301), (1879 / 282750), 150, false, 376, true⟩, (5569411 / 1000000000000)),
  (⟨(1879 / 282750), (5 / 752), 150, false, 376, false⟩, (20593651 / 1000000000000)),
  (⟨(5 / 752), (1 / 150), 150, false, 375, false⟩, (5873227 / 62500000000)),
  (⟨(1 / 150), (1246 / 186875), 149, true, 374, true⟩, (1284281 / 200000000000)),
  (⟨(1246 / 186875), (5 / 748), 149, true, 374, false⟩, (113883113 / 1000000000000)),
  (⟨(5 / 748), (2 / 299), 149, true, 373, false⟩, (27386297 / 1000000000000)),
  (⟨(2 / 299), (932 / 139315), 149, false, 373, true⟩, (5473509 / 1000000000000))]

theorem fits : cappedChainFits (5 / 854) cells := by
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

theorem endpoint : cappedChainEnd (5 / 854) cells = (932 / 139315) := by rfl

theorem upper : cappedChainUpper cells = (5035689209 / 1000000000000) := by
  norm_num [cappedChainUpper, cells]

theorem bound :
    IntervalIntegrable middleRankProfile MeasureTheory.volume ((5 / 854) : ℝ) ((932 / 139315) : ℝ) ∧
    (∫ β in ((5 / 854) : ℝ)..((932 / 139315) : ℝ), middleRankProfile β) ≤ ((5035689209 / 1000000000000) : ℝ) := by
  have h := integrate_cappedChain fits
  rw [endpoint, upper] at h
  norm_num at h ⊢
  exact h

end Block16
end Zeta5.Certificate.ExtendedArithmetic
