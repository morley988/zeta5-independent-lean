import Zeta5.Certificate.ExtendedArithmetic.Core

namespace Zeta5.Certificate.ExtendedArithmetic

namespace Block03

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def cells : List (ArithmeticCell × ℚ) := [
  (⟨(1 / 448), (2797 / 1253000), 447, true, 1119, true⟩, (718277 / 1000000000000)),
  (⟨(2797 / 1253000), (5 / 2238), 447, true, 1119, false⟩, (6372061 / 500000000000)),
  (⟨(5 / 2238), (2 / 895), 447, true, 1118, false⟩, (1528949 / 500000000000)),
  (⟨(2 / 895), (621 / 277885), 447, false, 1118, true⟩, (7539 / 12500000000)),
  (⟨(621 / 277885), (5 / 2236), 447, false, 1118, false⟩, (7902209 / 1000000000000)),
  (⟨(5 / 2236), (1 / 447), 447, false, 1117, false⟩, (5052567 / 1000000000000)),
  (⟨(1 / 447), (5584 / 2495935), 446, true, 1117, true⟩, (18231 / 25000000000)),
  (⟨(5584 / 2495935), (5 / 2234), 446, true, 1117, false⟩, (1255729 / 200000000000)),
  (⟨(5 / 2234), (2 / 893), 446, true, 1116, false⟩, (9586649 / 1000000000000)),
  (⟨(2 / 893), (5579 / 2490910), 446, false, 1116, true⟩, (122461 / 200000000000)),
  (⟨(5579 / 2490910), (5 / 2232), 446, false, 1116, false⟩, (117909 / 50000000000)),
  (⟨(5 / 2232), (1 / 446), 446, false, 1115, false⟩, (1331027 / 125000000000)),
  (⟨(1 / 446), (11138 / 4967325), 445, true, 1114, true⟩, (724737 / 1000000000000)),
  (⟨(11138 / 4967325), (5 / 2228), 445, true, 1114, false⟩, (12858727 / 1000000000000)),
  (⟨(5 / 2228), (2 / 891), 445, true, 1113, false⟩, (3085413 / 1000000000000)),
  (⟨(2 / 891), (2782 / 1239325), 445, false, 1113, true⟩, (121713 / 200000000000)),
  (⟨(2782 / 1239325), (5 / 2226), 445, false, 1113, false⟩, (7973331 / 1000000000000)),
  (⟨(5 / 2226), (1 / 445), 445, false, 1112, false⟩, (203923 / 40000000000)),
  (⟨(1 / 445), (3706 / 1649095), 444, true, 1112, true⟩, (91981 / 125000000000)),
  (⟨(3706 / 1649095), (5 / 2224), 444, true, 1112, false⟩, (6335187 / 1000000000000)),
  (⟨(5 / 2224), (2 / 889), 444, true, 1111, false⟩, (9673083 / 1000000000000)),
  (⟨(2 / 889), (2777 / 1234320), 444, false, 1111, true⟩, (4943 / 8000000000)),
  (⟨(2777 / 1234320), (5 / 2222), 444, false, 1111, false⟩, (1189703 / 500000000000)),
  (⟨(5 / 2222), (1 / 444), 444, false, 1110, false⟩, (5372159 / 500000000000)),
  (⟨(1 / 444), (1848 / 820475), 443, true, 1109, true⟩, (182821 / 250000000000)),
  (⟨(1848 / 820475), (5 / 2218), 443, true, 1109, false⟩, (2594977 / 200000000000)),
  (⟨(5 / 2218), (2 / 887), 443, true, 1108, false⟩, (31133 / 10000000000)),
  (⟨(2 / 887), (5539 / 2456435), 443, false, 1108, true⟩, (153521 / 250000000000)),
  (⟨(5539 / 2456435), (5 / 2216), 443, false, 1108, false⟩, (1005677 / 125000000000)),
  (⟨(5 / 2216), (1 / 443), 443, false, 1107, false⟩, (5144201 / 1000000000000)),
  (⟨(1 / 443), (2767 / 1225725), 442, true, 1107, true⟩, (742547 / 1000000000000)),
  (⟨(2767 / 1225725), (5 / 2214), 442, true, 1107, false⟩, (399531 / 62500000000)),
  (⟨(5 / 2214), (2 / 885), 442, true, 1106, false⟩, (9760691 / 1000000000000)),
  (⟨(2 / 885), (1843 / 815490), 442, false, 1106, true⟩, (623521 / 1000000000000)),
  (⟨(1843 / 815490), (5 / 2212), 442, false, 1106, false⟩, (60023 / 25000000000)),
  (⟨(5 / 2212), (1 / 442), 442, false, 1105, false⟩, (84701 / 7812500000)),
  (⟨(1 / 442), (11038 / 4878575), 441, true, 1104, true⟩, (737921 / 1000000000000)),
  (⟨(11038 / 4878575), (5 / 2208), 441, true, 1104, false⟩, (818289 / 62500000000)),
  (⟨(5 / 2208), (2 / 883), 441, true, 1103, false⟩, (3141567 / 1000000000000)),
  (⟨(2 / 883), (919 / 405720), 441, false, 1103, true⟩, (309839 / 500000000000)),
  (⟨(919 / 405720), (5 / 2206), 441, false, 1103, false⟩, (2029621 / 250000000000)),
  (⟨(5 / 2206), (1 / 441), 441, false, 1102, false⟩, (1297739 / 250000000000)),
  (⟨(1 / 441), (11018 / 4858715), 440, true, 1102, true⟩, (374669 / 500000000000)),
  (⟨(11018 / 4858715), (5 / 2204), 440, true, 1102, false⟩, (3225293 / 500000000000)),
  (⟨(5 / 2204), (2 / 881), 440, true, 1101, false⟩, (1969899 / 200000000000)),
  (⟨(2 / 881), (344 / 151525), 440, false, 1101, true⟩, (125849 / 200000000000)),
  (⟨(344 / 151525), (5 / 2202), 440, false, 1101, false⟩, (2422727 / 1000000000000)),
  (⟨(5 / 2202), (1 / 440), 440, false, 1100, false⟩, (2735117 / 250000000000)),
  (⟨(1 / 440), (2747 / 1208625), 439, true, 1099, true⟩, (93081 / 125000000000)),
  (⟨(2747 / 1208625), (5 / 2198), 439, true, 1099, false⟩, (13211973 / 1000000000000)),
  (⟨(5 / 2198), (2 / 879), 439, true, 1098, false⟩, (3170221 / 1000000000000)),
  (⟨(2 / 879), (5489 / 2412305), 439, false, 1098, true⟩, (625349 / 1000000000000)),
  (⟨(5489 / 2412305), (5 / 2196), 439, false, 1098, false⟩, (1024069 / 125000000000)),
  (⟨(5 / 2196), (1 / 439), 439, false, 1097, false⟩, (5238351 / 1000000000000)),
  (⟨(1 / 439), (1828 / 802455), 438, true, 1097, true⟩, (378111 / 500000000000)),
  (⟨(1828 / 802455), (5 / 2194), 438, true, 1097, false⟩, (203421 / 31250000000)),
  (⟨(5 / 2194), (2 / 877), 438, true, 1096, false⟩, (2484879 / 250000000000)),
  (⟨(2 / 877), (5479 / 2402430), 438, false, 1096, true⟩, (635047 / 1000000000000)),
  (⟨(5479 / 2402430), (5 / 2192), 438, false, 1096, false⟩, (2444833 / 1000000000000)),
  (⟨(5 / 2192), (1 / 438), 438, false, 1095, false⟩, (11040563 / 1000000000000)),
  (⟨(1 / 438), (3646 / 1596875), 437, true, 1094, true⟩, (187867 / 250000000000)),
  (⟨(3646 / 1596875), (5 / 2188), 437, true, 1094, false⟩, (6666481 / 500000000000)),
  (⟨(5 / 2188), (2 / 875), 437, true, 1093, false⟩, (3199269 / 1000000000000)),
  (⟨(2 / 875), (2732 / 1195195), 437, false, 1093, true⟩, (631099 / 1000000000000)),
  (⟨(2732 / 1195195), (5 / 2186), 437, false, 1093, false⟩, (4133819 / 500000000000)),
  (⟨(5 / 2186), (1 / 437), 437, false, 1092, false⟩, (2643199 / 500000000000)),
  (⟨(1 / 437), (10918 / 4770945), 436, true, 1092, true⟩, (763201 / 1000000000000)),
  (⟨(10918 / 4770945), (5 / 2184), 436, true, 1092, false⟩, (410573 / 62500000000)),
  (⟨(5 / 2184), (2 / 873), 436, true, 1091, false⟩, (10030777 / 1000000000000)),
  (⟨(2 / 873), (909 / 396760), 436, false, 1091, true⟩, (640931 / 1000000000000)),
  (⟨(909 / 396760), (5 / 2182), 436, false, 1091, false⟩, (1233621 / 500000000000)),
  (⟨(5 / 2182), (1 / 436), 436, false, 1090, false⟩, (5571019 / 500000000000)),
  (⟨(1 / 436), (5444 / 2373475), 435, true, 1089, true⟩, (379191 / 500000000000)),
  (⟨(5444 / 2373475), (5 / 2178), 435, true, 1089, false⟩, (672781 / 50000000000)),
  (⟨(5 / 2178), (2 / 871), 435, true, 1088, false⟩, (1614359 / 500000000000)),
  (⟨(2 / 871), (1813 / 789525), 435, false, 1088, true⟩, (311 / 488281250)),
  (⟨(1813 / 789525), (5 / 2176), 435, false, 1088, false⟩, (104297 / 12500000000)),
  (⟨(5 / 2176), (1 / 435), 435, false, 1087, false⟩, (5335109 / 1000000000000)),
  (⟨(1 / 435), (247 / 107440), 434, true, 1087, true⟩, (385139 / 500000000000)),
  (⟨(247 / 107440), (5 / 2174), 434, true, 1087, false⟩, (6629689 / 1000000000000)),
  (⟨(5 / 2174), (2 / 869), 434, true, 1086, false⟩, (10123301 / 1000000000000)),
  (⟨(2 / 869), (5429 / 2358790), 434, false, 1086, true⟩, (646897 / 1000000000000)),
  (⟨(5429 / 2358790), (5 / 2172), 434, false, 1086, false⟩, (2489961 / 1000000000000)),
  (⟨(5 / 2172), (1 / 434), 434, false, 1085, false⟩, (11244919 / 1000000000000)),
  (⟨(1 / 434), (10838 / 4703475), 433, true, 1084, true⟩, (47837 / 62500000000)),
  (⟨(10838 / 4703475), (5 / 2168), 433, true, 1084, false⟩, (6789989 / 500000000000)),
  (⟨(5 / 2168), (2 / 867), 433, true, 1083, false⟩, (130343 / 40000000000)),
  (⟨(2 / 867), (2707 / 1173430), 433, false, 1083, true⟩, (321419 / 500000000000)),
  (⟨(2707 / 1173430), (5 / 2166), 433, false, 1083, false⟩, (421047 / 50000000000)),
  (⟨(5 / 2166), (1 / 433), 433, false, 1082, false⟩, (336531 / 62500000000)),
  (⟨(1 / 433), (3606 / 1561325), 432, true, 1082, true⟩, (388727 / 500000000000)),
  (⟨(3606 / 1561325), (5 / 2164), 432, true, 1082, false⟩, (133821 / 20000000000)),
  (⟨(5 / 2164), (2 / 865), 432, true, 1081, false⟩, (10217111 / 1000000000000)),
  (⟨(2 / 865), (1351 / 584280), 432, false, 1081, true⟩, (326473 / 500000000000)),
  (⟨(1351 / 584280), (5 / 2162), 432, false, 1081, false⟩, (502599 / 200000000000)),
  (⟨(5 / 2162), (1 / 432), 432, false, 1080, false⟩, (11349231 / 1000000000000)),
  (⟨(1 / 432), (899 / 388350), 431, true, 1079, true⟩, (309 / 400000000)),
  (⟨(899 / 388350), (5 / 2158), 431, true, 1079, false⟩, (13706069 / 1000000000000)),
  (⟨(5 / 2158), (2 / 863), 431, true, 1078, false⟩, (3288849 / 1000000000000)),
  (⟨(2 / 863), (5389 / 2325245), 431, false, 1078, true⟩, (648831 / 1000000000000)),
  (⟨(5389 / 2325245), (5 / 2156), 431, false, 1078, false⟩, (4249597 / 500000000000)),
  (⟨(5 / 2156), (1 / 431), 431, false, 1077, false⟩, (5434573 / 1000000000000)),
  (⟨(1 / 431), (5384 / 2320395), 430, true, 1077, true⟩, (78473 / 100000000000)),
  (⟨(5384 / 2320395), (5 / 2154), 430, true, 1077, false⟩, (6753267 / 1000000000000)),
  (⟨(5 / 2154), (2 / 861), 430, true, 1076, false⟩, (10312231 / 1000000000000)),
  (⟨(2 / 861), (1793 / 771850), 430, false, 1076, true⟩, (16477 / 25000000000)),
  (⟨(1793 / 771850), (5 / 2152), 430, false, 1076, false⟩, (2536351 / 1000000000000)),
  (⟨(5 / 2152), (1 / 430), 430, false, 1075, false⟩, (5727501 / 500000000000)),
  (⟨(1 / 430), (10738 / 4617125), 429, true, 1074, true⟩, (389853 / 500000000000)),
  (⟨(10738 / 4617125), (5 / 2148), 429, true, 1074, false⟩, (13833923 / 1000000000000)),
  (⟨(5 / 2148), (2 / 859), 429, true, 1073, false⟩, (1659773 / 500000000000)),
  (⟨(2 / 859), (298 / 127985), 429, false, 1073, true⟩, (163727 / 250000000000)),
  (⟨(298 / 127985), (5 / 2146), 429, false, 1073, false⟩, (1715709 / 200000000000)),
  (⟨(5 / 2146), (1 / 429), 429, false, 1072, false⟩, (5485351 / 1000000000000)),
  (⟨(1 / 429), (10718 / 4597805), 428, true, 1072, true⟩, (198027 / 250000000000)),
  (⟨(10718 / 4597805), (5 / 2144), 428, true, 1072, false⟩, (1704089 / 250000000000)),
  (⟨(5 / 2144), (2 / 857), 428, true, 1071, false⟩, (2081737 / 200000000000)),
  (⟨(2 / 857), (2677 / 1147040), 428, false, 1071, true⟩, (332651 / 500000000000)),
  (⟨(2677 / 1147040), (5 / 2142), 428, false, 1071, false⟩, (2560033 / 1000000000000)),
  (⟨(5 / 2142), (1 / 428), 428, false, 1070, false⟩, (5781129 / 500000000000)),
  (⟨(1 / 428), (5344 / 2287125), 427, true, 1069, true⟩, (157403 / 200000000000)),
  (⟨(5344 / 2287125), (5 / 2138), 427, true, 1069, false⟩, (1745447 / 125000000000)),
  (⟨(5 / 2138), (2 / 855), 427, true, 1068, false⟩, (134027 / 40000000000)),
  (⟨(2 / 855), (5339 / 2282315), 427, false, 1068, true⟩, (661071 / 1000000000000)),
  (⟨(5339 / 2282315), (5 / 2136), 427, false, 1068, false⟩, (8659013 / 1000000000000)),
  (⟨(5 / 2136), (1 / 427), 427, false, 1067, false⟩, (1384211 / 250000000000)),
  (⟨(1 / 427), (889 / 379585), 426, true, 1067, true⟩, (99949 / 125000000000)),
  (⟨(889 / 379585), (5 / 2134), 426, true, 1067, false⟩, (6880333 / 1000000000000))]

theorem fits : cappedChainFits (1 / 448) cells := by
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

theorem endpoint : cappedChainEnd (1 / 448) cells = (5 / 2134) := by rfl

theorem upper : cappedChainUpper cells = (334453589 / 500000000000) := by
  norm_num [cappedChainUpper, cells]

theorem bound :
    IntervalIntegrable middleRankProfile MeasureTheory.volume ((1 / 448) : ℝ) ((5 / 2134) : ℝ) ∧
    (∫ β in ((1 / 448) : ℝ)..((5 / 2134) : ℝ), middleRankProfile β) ≤ ((334453589 / 500000000000) : ℝ) := by
  have h := integrate_cappedChain fits
  rw [endpoint, upper] at h
  norm_num at h ⊢
  exact h

end Block03
end Zeta5.Certificate.ExtendedArithmetic
