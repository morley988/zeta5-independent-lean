import Zeta5.Certificate.ExtendedArithmetic.Core

namespace Zeta5.Certificate.ExtendedArithmetic

namespace Block15

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def cells : List (ArithmeticCell × ℚ) := [
  (⟨(1 / 192), (399 / 76600), 191, true, 479, true⟩, (78329 / 20000000000)),
  (⟨(399 / 76600), (5 / 958), 191, true, 479, false⟩, (17366971 / 250000000000)),
  (⟨(5 / 958), (2 / 383), 191, true, 478, false⟩, (8346643 / 500000000000)),
  (⟨(2 / 383), (2389 / 457445), 191, false, 478, true⟩, (3321891 / 1000000000000)),
  (⟨(2389 / 457445), (5 / 956), 191, false, 478, false⟩, (21584319 / 500000000000)),
  (⟨(5 / 956), (1 / 191), 191, false, 477, false⟩, (5531337 / 200000000000)),
  (⟨(1 / 191), (2384 / 455295), 190, true, 477, true⟩, (162279 / 40000000000)),
  (⟨(2384 / 455295), (5 / 954), 190, true, 477, false⟩, (8588211 / 250000000000)),
  (⟨(5 / 954), (2 / 381), 190, true, 476, false⟩, (13154311 / 250000000000)),
  (⟨(2 / 381), (793 / 151050), 190, false, 476, true⟩, (860121 / 250000000000)),
  (⟨(793 / 151050), (5 / 952), 190, false, 476, false⟩, (12885501 / 1000000000000)),
  (⟨(5 / 952), (1 / 190), 190, false, 475, false⟩, (58602389 / 1000000000000)),
  (⟨(1 / 190), (4738 / 900125), 189, true, 474, true⟩, (799889 / 200000000000)),
  (⟨(4738 / 900125), (5 / 948), 189, true, 474, false⟩, (70939631 / 1000000000000)),
  (⟨(5 / 948), (2 / 379), 189, true, 473, false⟩, (2130927 / 125000000000)),
  (⟨(2 / 379), (394 / 74655), 189, false, 473, true⟩, (3392917 / 1000000000000)),
  (⟨(394 / 74655), (5 / 946), 189, false, 473, false⟩, (44084979 / 1000000000000)),
  (⟨(5 / 946), (1 / 189), 189, false, 472, false⟩, (7061199 / 250000000000)),
  (⟨(1 / 189), (4718 / 891605), 188, true, 472, true⟩, (4144479 / 1000000000000)),
  (⟨(4718 / 891605), (5 / 944), 188, true, 472, false⟩, (1754153 / 50000000000)),
  (⟨(5 / 944), (2 / 377), 188, true, 471, false⟩, (53738817 / 1000000000000)),
  (⟨(2 / 377), (1177 / 221840), 188, false, 471, true⟩, (3515331 / 1000000000000)),
  (⟨(1177 / 221840), (5 / 942), 188, false, 471, false⟩, (6579537 / 500000000000)),
  (⟨(5 / 942), (1 / 188), 188, false, 470, false⟩, (59854543 / 1000000000000)),
  (⟨(1 / 188), (2344 / 440625), 187, true, 469, true⟩, (4085107 / 1000000000000)),
  (⟨(2344 / 440625), (5 / 938), 187, true, 469, false⟩, (9057331 / 125000000000)),
  (⟨(5 / 938), (2 / 375), 187, true, 468, false⟩, (2176617 / 125000000000)),
  (⟨(2 / 375), (2339 / 438515), 187, false, 468, true⟩, (693249 / 200000000000)),
  (⟨(2339 / 438515), (5 / 936), 187, false, 468, false⟩, (45030809 / 1000000000000)),
  (⟨(5 / 936), (1 / 187), 187, false, 467, false⟩, (7212967 / 250000000000)),
  (⟨(1 / 187), (389 / 72735), 186, true, 467, true⟩, (846969 / 200000000000)),
  (⟨(389 / 72735), (5 / 934), 186, true, 467, false⟩, (4479601 / 125000000000)),
  (⟨(5 / 934), (2 / 373), 186, true, 466, false⟩, (54896637 / 1000000000000)),
  (⟨(2 / 373), (2329 / 434310), 186, false, 466, true⟩, (1796323 / 500000000000)),
  (⟨(2329 / 434310), (5 / 932), 186, false, 466, false⟩, (3360363 / 250000000000)),
  (⟨(5 / 932), (1 / 186), 186, false, 465, false⟩, (30573631 / 500000000000)),
  (⟨(1 / 186), (1546 / 287525), 185, true, 464, true⟩, (4173551 / 1000000000000)),
  (⟨(1546 / 287525), (5 / 928), 185, true, 464, false⟩, (37013491 / 500000000000)),
  (⟨(5 / 928), (2 / 371), 185, true, 463, false⟩, (17790339 / 1000000000000)),
  (⟨(2 / 371), (1157 / 214600), 185, false, 463, true⟩, (141679 / 40000000000)),
  (⟨(1157 / 214600), (5 / 926), 185, false, 463, false⟩, (2875463 / 62500000000)),
  (⟨(5 / 926), (1 / 185), 185, false, 462, false⟩, (29478723 / 1000000000000)),
  (⟨(1 / 185), (4618 / 854235), 184, true, 462, true⟩, (4328197 / 1000000000000)),
  (⟨(4618 / 854235), (5 / 924), 184, true, 462, false⟩, (36615111 / 1000000000000)),
  (⟨(5 / 924), (2 / 369), 184, true, 461, false⟩, (28046141 / 500000000000)),
  (⟨(2 / 369), (48 / 8855), 184, false, 461, true⟩, (3672539 / 1000000000000)),
  (⟨(48 / 8855), (5 / 922), 184, false, 461, false⟩, (13733017 / 1000000000000)),
  (⟨(5 / 922), (1 / 184), 184, false, 460, false⟩, (62482317 / 1000000000000)),
  (⟨(1 / 184), (1147 / 211025), 183, true, 459, true⟩, (2132449 / 500000000000)),
  (⟨(1147 / 211025), (5 / 918), 183, true, 459, false⟩, (9455849 / 125000000000)),
  (⟨(5 / 918), (2 / 367), 183, true, 458, false⟩, (9090073 / 500000000000)),
  (⟨(2 / 367), (763 / 139995), 183, false, 458, true⟩, (724043 / 200000000000)),
  (⟨(763 / 139995), (5 / 916), 183, false, 458, false⟩, (376129 / 8000000000)),
  (⟨(5 / 916), (1 / 183), 183, false, 457, false⟩, (3765779 / 125000000000)),
  (⟨(1 / 183), (2284 / 417925), 182, true, 457, true⟩, (4424671 / 1000000000000)),
  (⟨(2284 / 417925), (5 / 914), 182, true, 457, false⟩, (37419047 / 1000000000000)),
  (⟨(5 / 914), (2 / 365), 182, true, 456, false⟩, (57327419 / 1000000000000)),
  (⟨(2 / 365), (2279 / 415870), 182, false, 456, true⟩, (1877563 / 500000000000)),
  (⟨(2279 / 415870), (5 / 912), 182, false, 456, false⟩, (14034173 / 1000000000000)),
  (⟨(5 / 912), (1 / 182), 182, false, 455, false⟩, (31930789 / 500000000000)),
  (⟨(1 / 182), (4538 / 825825), 181, true, 454, true⟩, (2179639 / 500000000000)),
  (⟨(4538 / 825825), (5 / 908), 181, true, 454, false⟩, (19330089 / 250000000000)),
  (⟨(5 / 908), (2 / 363), 181, true, 453, false⟩, (9291453 / 500000000000)),
  (⟨(2 / 363), (1132 / 205435), 181, false, 453, true⟩, (3701077 / 1000000000000)),
  (⟨(1132 / 205435), (5 / 906), 181, false, 453, false⟩, (48058383 / 1000000000000)),
  (⟨(5 / 906), (1 / 181), 181, false, 452, false⟩, (1924707 / 62500000000)),
  (⟨(1 / 181), (1506 / 272555), 180, true, 452, true⟩, (904881 / 200000000000)),
  (⟨(1506 / 272555), (5 / 904), 180, true, 452, false⟩, (38249753 / 1000000000000)),
  (⟨(5 / 904), (2 / 361), 180, true, 451, false⟩, (11720761 / 200000000000)),
  (⟨(2 / 361), (1127 / 203400), 180, false, 451, true⟩, (3840529 / 1000000000000)),
  (⟨(1127 / 203400), (5 / 902), 180, false, 451, false⟩, (2869069 / 200000000000)),
  (⟨(5 / 902), (1 / 180), 180, false, 450, false⟩, (65287017 / 1000000000000)),
  (⟨(1 / 180), (748 / 134625), 179, true, 449, true⟩, (178273 / 40000000000)),
  (⟨(748 / 134625), (5 / 898), 179, true, 449, false⟩, (79050077 / 1000000000000)),
  (⟨(5 / 898), (2 / 359), 179, true, 448, false⟩, (23749 / 1250000000)),
  (⟨(2 / 359), (2239 / 401855), 179, false, 448, true⟩, (3784677 / 1000000000000)),
  (⟨(2239 / 401855), (5 / 896), 179, false, 448, false⟩, (24567843 / 500000000000)),
  (⟨(5 / 896), (1 / 179), 179, false, 447, false⟩, (7871733 / 250000000000)),
  (⟨(1 / 179), (1117 / 199920), 178, true, 447, true⟩, (92551 / 20000000000)),
  (⟨(1117 / 199920), (5 / 894), 178, true, 447, false⟩, (2444277 / 62500000000)),
  (⟨(5 / 894), (2 / 357), 178, true, 446, false⟩, (59923299 / 1000000000000)),
  (⟨(2 / 357), (743 / 132610), 178, false, 446, true⟩, (1964439 / 500000000000)),
  (⟨(743 / 132610), (5 / 892), 178, false, 446, false⟩, (14666981 / 1000000000000)),
  (⟨(5 / 892), (1 / 178), 178, false, 445, false⟩, (834509 / 12500000000)),
  (⟨(1 / 178), (4438 / 789875), 177, true, 444, true⟩, (1139421 / 250000000000)),
  (⟨(4438 / 789875), (5 / 888), 177, true, 444, false⟩, (2526203 / 31250000000)),
  (⟨(5 / 888), (2 / 355), 177, true, 443, false⟩, (19429641 / 1000000000000)),
  (⟨(2 / 355), (123 / 21830), 177, false, 443, true⟩, (3871143 / 1000000000000)),
  (⟨(123 / 21830), (5 / 886), 177, false, 443, false⟩, (6281203 / 125000000000)),
  (⟨(5 / 886), (1 / 177), 177, false, 442, false⟩, (6440423 / 200000000000)),
  (⟨(1 / 177), (4418 / 781895), 176, true, 442, true⟩, (4734261 / 1000000000000)),
  (⟨(4418 / 781895), (5 / 884), 176, true, 442, false⟩, (7999271 / 200000000000)),
  (⟨(5 / 884), (2 / 353), 176, true, 441, false⟩, (61287863 / 1000000000000)),
  (⟨(2 / 353), (551 / 97240), 176, false, 441, true⟩, (4020309 / 1000000000000)),
  (⟨(551 / 97240), (5 / 882), 176, false, 441, false⟩, (14999557 / 1000000000000)),
  (⟨(5 / 882), (1 / 176), 176, false, 440, false⟩, (6828489 / 100000000000)),
  (⟨(1 / 176), (1097 / 193050), 175, true, 439, true⟩, (932401 / 200000000000)),
  (⟨(1097 / 193050), (5 / 878), 175, true, 439, false⟩, (41344151 / 500000000000)),
  (⟨(5 / 878), (2 / 351), 175, true, 438, false⟩, (9937439 / 500000000000)),
  (⟨(2 / 351), (2189 / 384125), 175, false, 438, true⟩, (1980303 / 500000000000)),
  (⟨(2189 / 384125), (5 / 876), 175, false, 438, false⟩, (12850469 / 250000000000)),
  (⟨(5 / 876), (1 / 175), 175, false, 437, false⟩, (4117743 / 125000000000)),
  (⟨(1 / 175), (728 / 127385), 174, true, 437, true⟩, (2422353 / 500000000000)),
  (⟨(728 / 127385), (5 / 874), 174, true, 437, false⟩, (40914863 / 1000000000000)),
  (⟨(5 / 874), (2 / 349), 174, true, 436, false⟩, (31349787 / 500000000000)),
  (⟨(2 / 349), (2179 / 380190), 174, false, 436, true⟩, (4114969 / 1000000000000)),
  (⟨(2179 / 380190), (5 / 872), 174, false, 436, false⟩, (7671787 / 500000000000)),
  (⟨(5 / 872), (1 / 174), 174, false, 435, false⟩, (69861859 / 1000000000000)),
  (⟨(1 / 174), (1446 / 251575), 173, true, 434, true⟩, (95399 / 20000000000)),
  (⟨(1446 / 251575), (5 / 868), 173, true, 434, false⟩, (42301167 / 500000000000)),
  (⟨(5 / 868), (2 / 347), 173, true, 433, false⟩, (5083899 / 250000000000)),
  (⟨(2 / 347), (1082 / 187705), 173, false, 433, true⟩, (2026603 / 500000000000)),
  (⟨(1082 / 187705), (5 / 866), 173, false, 433, false⟩, (52594221 / 1000000000000)),
  (⟨(5 / 866), (1 / 173), 173, false, 432, false⟩, (16853783 / 500000000000)),
  (⟨(1 / 173), (4318 / 746925), 172, true, 432, true⟩, (4959061 / 1000000000000)),
  (⟨(4318 / 746925), (5 / 864), 172, true, 432, false⟩, (20932689 / 500000000000)),
  (⟨(5 / 864), (2 / 345), 172, true, 431, false⟩, (64160629 / 1000000000000)),
  (⟨(2 / 345), (359 / 61920), 172, false, 431, true⟩, (421301 / 100000000000)),
  (⟨(359 / 61920), (5 / 862), 172, false, 431, false⟩, (7849781 / 500000000000)),
  (⟨(5 / 862), (1 / 172), 172, false, 430, false⟩, (17873523 / 250000000000)),
  (⟨(1 / 172), (2144 / 368725), 171, true, 429, true⟩, (4881687 / 1000000000000)),
  (⟨(2144 / 368725), (5 / 858), 171, true, 429, false⟩, (86583601 / 1000000000000)),
  (⟨(5 / 858), (2 / 343), 171, true, 428, false⟩, (20812521 / 1000000000000)),
  (⟨(2 / 343), (713 / 122265), 171, false, 428, true⟩, (1037273 / 250000000000)),
  (⟨(713 / 122265), (5 / 856), 171, false, 428, false⟩, (53828539 / 1000000000000)),
  (⟨(5 / 856), (1 / 171), 171, false, 427, false⟩, (1078131 / 31250000000)),
  (⟨(1 / 171), (97 / 16585), 170, true, 427, true⟩, (634689 / 125000000000)),
  (⟨(97 / 16585), (5 / 854), 170, true, 427, false⟩, (21424703 / 500000000000))]

theorem fits : cappedChainFits (1 / 192) cells := by
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

theorem endpoint : cappedChainEnd (1 / 192) cells = (5 / 854) := by rfl

theorem upper : cappedChainUpper cells = (3899974557 / 1000000000000) := by
  norm_num [cappedChainUpper, cells]

theorem bound :
    IntervalIntegrable middleRankProfile MeasureTheory.volume ((1 / 192) : ℝ) ((5 / 854) : ℝ) ∧
    (∫ β in ((1 / 192) : ℝ)..((5 / 854) : ℝ), middleRankProfile β) ≤ ((3899974557 / 1000000000000) : ℝ) := by
  have h := integrate_cappedChain fits
  rw [endpoint, upper] at h
  norm_num at h ⊢
  exact h

end Block15
end Zeta5.Certificate.ExtendedArithmetic
