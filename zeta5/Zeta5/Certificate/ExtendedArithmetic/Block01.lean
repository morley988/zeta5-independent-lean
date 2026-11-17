import Zeta5.Certificate.ExtendedArithmetic.Core

namespace Zeta5.Certificate.ExtendedArithmetic

namespace Block01

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def cells : List (ArithmeticCell × ℚ) := [
  (⟨(5 / 2454), (2 / 981), 490, true, 1226, false⟩, (3972171 / 500000000000)),
  (⟨(2 / 981), (2043 / 1002050), 490, false, 1226, true⟩, (506607 / 1000000000000)),
  (⟨(2043 / 1002050), (5 / 2452), 490, false, 1226, false⟩, (78191 / 40000000000)),
  (⟨(5 / 2452), (1 / 490), 490, false, 1225, false⟩, (8822453 / 1000000000000)),
  (⟨(1 / 490), (12238 / 5996375), 489, true, 1224, true⟩, (600363 / 1000000000000)),
  (⟨(12238 / 5996375), (5 / 2448), 489, true, 1224, false⟩, (426089 / 40000000000)),
  (⟨(5 / 2448), (2 / 979), 489, true, 1223, false⟩, (2555713 / 1000000000000)),
  (⟨(2 / 979), (1019 / 498780), 489, false, 1223, true⟩, (503783 / 1000000000000)),
  (⟨(1019 / 498780), (5 / 2446), 489, false, 1223, false⟩, (660417 / 100000000000)),
  (⟨(5 / 2446), (1 / 489), 489, false, 1222, false⟩, (4222077 / 1000000000000)),
  (⟨(1 / 489), (12218 / 5974355), 488, true, 1222, true⟩, (608737 / 1000000000000)),
  (⟨(12218 / 5974355), (5 / 2444), 488, true, 1222, false⟩, (5246771 / 1000000000000)),
  (⟨(5 / 2444), (2 / 977), 488, true, 1221, false⟩, (4004753 / 500000000000)),
  (⟨(2 / 977), (763 / 372710), 488, false, 1221, true⟩, (127699 / 250000000000)),
  (⟨(763 / 372710), (5 / 2442), 488, false, 1221, false⟩, (394157 / 200000000000)),
  (⟨(5 / 2442), (1 / 488), 488, false, 1220, false⟩, (4447443 / 500000000000)),
  (⟨(1 / 488), (3047 / 1486875), 487, true, 1219, true⟩, (605297 / 1000000000000)),
  (⟨(3047 / 1486875), (5 / 2438), 487, true, 1219, false⟩, (5369877 / 500000000000)),
  (⟨(5 / 2438), (2 / 975), 487, true, 1218, false⟩, (644181 / 250000000000)),
  (⟨(2 / 975), (6089 / 2968265), 487, false, 1218, true⟩, (253969 / 500000000000)),
  (⟨(6089 / 2968265), (5 / 2436), 487, false, 1218, false⟩, (1664619 / 250000000000)),
  (⟨(5 / 2436), (1 / 487), 487, false, 1217, false⟩, (4256819 / 1000000000000)),
  (⟨(1 / 487), (2028 / 987595), 486, true, 1217, true⟩, (24551 / 40000000000)),
  (⟨(2028 / 987595), (5 / 2434), 486, true, 1217, false⟩, (5289939 / 1000000000000)),
  (⟨(5 / 2434), (2 / 973), 486, true, 1216, false⟩, (323019 / 40000000000)),
  (⟨(2 / 973), (6079 / 2957310), 486, false, 1216, true⟩, (257519 / 500000000000)),
  (⟨(6079 / 2957310), (5 / 2432), 486, false, 1216, false⟩, (124187 / 62500000000)),
  (⟨(5 / 2432), (1 / 486), 486, false, 1215, false⟩, (1121027 / 125000000000)),
  (⟨(1 / 486), (4046 / 1966275), 485, true, 1214, true⟩, (152573 / 250000000000)),
  (⟨(4046 / 1966275), (5 / 2428), 485, true, 1214, false⟩, (2165673 / 200000000000)),
  (⟨(5 / 2428), (2 / 971), 485, true, 1213, false⟩, (519599 / 200000000000)),
  (⟨(2 / 971), (3032 / 1471975), 485, false, 1213, true⟩, (32009 / 62500000000)),
  (⟨(3032 / 1471975), (5 / 2426), 485, false, 1213, false⟩, (419591 / 62500000000)),
  (⟨(5 / 2426), (1 / 485), 485, false, 1212, false⟩, (536499 / 125000000000)),
  (⟨(1 / 485), (12118 / 5876985), 484, true, 1212, true⟩, (4951 / 8000000000)),
  (⟨(12118 / 5876985), (5 / 2424), 484, true, 1212, false⟩, (2666821 / 500000000000)),
  (⟨(5 / 2424), (2 / 969), 484, true, 1211, false⟩, (4071131 / 500000000000)),
  (⟨(2 / 969), (1009 / 488840), 484, false, 1211, true⟩, (129833 / 250000000000)),
  (⟨(1009 / 488840), (5 / 2422), 484, false, 1211, false⟩, (10017 / 5000000000)),
  (⟨(5 / 2422), (1 / 484), 484, false, 1210, false⟩, (1130307 / 125000000000)),
  (⟨(1 / 484), (6044 / 2925175), 483, true, 1209, true⟩, (153837 / 250000000000)),
  (⟨(6044 / 2925175), (5 / 2418), 483, true, 1209, false⟩, (5459039 / 500000000000)),
  (⟨(5 / 2418), (2 / 967), 483, true, 1208, false⟩, (261953 / 100000000000)),
  (⟨(2 / 967), (671 / 324415), 483, false, 1208, true⟩, (258201 / 500000000000)),
  (⟨(671 / 324415), (5 / 2416), 483, false, 1208, false⟩, (6769119 / 1000000000000)),
  (⟨(5 / 2416), (1 / 483), 483, false, 1207, false⟩, (4327603 / 1000000000000)),
  (⟨(1 / 483), (3017 / 1457150), 482, true, 1207, true⟩, (312019 / 500000000000)),
  (⟨(3017 / 1457150), (5 / 2414), 482, true, 1207, false⟩, (168059 / 31250000000)),
  (⟨(5 / 2414), (2 / 965), 482, true, 1206, false⟩, (4104941 / 500000000000)),
  (⟨(2 / 965), (6029 / 2908870), 482, false, 1206, true⟩, (3273 / 6250000000)),
  (⟨(6029 / 2908870), (5 / 2412), 482, false, 1206, false⟩, (505003 / 250000000000)),
  (⟨(5 / 2412), (1 / 482), 482, false, 1205, false⟩, (9117621 / 1000000000000)),
  (⟨(1 / 482), (12038 / 5802075), 481, true, 1204, true⟩, (155117 / 250000000000)),
  (⟨(12038 / 5802075), (5 / 2408), 481, true, 1204, false⟩, (11008911 / 1000000000000)),
  (⟨(5 / 2408), (2 / 963), 481, true, 1203, false⟩, (528267 / 200000000000)),
  (⟨(2 / 963), (3007 / 1447810), 481, false, 1203, true⟩, (260357 / 500000000000)),
  (⟨(3007 / 1447810), (5 / 2406), 481, false, 1203, false⟩, (6825477 / 1000000000000)),
  (⟨(5 / 2406), (1 / 481), 481, false, 1202, false⟩, (2181829 / 500000000000)),
  (⟨(1 / 481), (4006 / 1926805), 480, true, 1202, true⟩, (629267 / 1000000000000)),
  (⟨(4006 / 1926805), (5 / 2404), 480, true, 1202, false⟩, (5422687 / 1000000000000)),
  (⟨(5 / 2404), (2 / 961), 480, true, 1201, false⟩, (8278347 / 1000000000000)),
  (⟨(2 / 961), (1501 / 721200), 480, false, 1201, true⟩, (528083 / 1000000000000)),
  (⟨(1501 / 721200), (5 / 2402), 480, false, 1201, false⟩, (63651 / 31250000000)),
  (⟨(5 / 2402), (1 / 480), 480, false, 1200, false⟩, (35913 / 3906250000)),
  (⟨(1 / 480), (999 / 479500), 479, true, 1199, true⟩, (156413 / 250000000000)),
  (⟨(999 / 479500), (5 / 2398), 479, true, 1199, false⟩, (11100881 / 1000000000000)),
  (⟨(5 / 2398), (2 / 959), 479, true, 1198, false⟩, (665853 / 250000000000)),
  (⟨(2 / 959), (5989 / 2871605), 479, false, 1198, true⟩, (13127 / 25000000000)),
  (⟨(5989 / 2871605), (5 / 2396), 479, false, 1198, false⟩, (3441271 / 500000000000)),
  (⟨(5 / 2396), (1 / 479), 479, false, 1197, false⟩, (2200083 / 500000000000)),
  (⟨(1 / 479), (544 / 260565), 478, true, 1197, true⟩, (317281 / 500000000000)),
  (⟨(544 / 260565), (5 / 2394), 478, true, 1197, false⟩, (5468049 / 1000000000000)),
  (⟨(5 / 2394), (2 / 957), 478, true, 1196, false⟩, (1043459 / 125000000000)),
  (⟨(2 / 957), (1993 / 953610), 478, false, 1196, true⟩, (266271 / 500000000000)),
  (⟨(1993 / 953610), (5 / 2392), 478, false, 1196, false⟩, (2053863 / 1000000000000)),
  (⟨(5 / 2392), (1 / 478), 478, false, 1195, false⟩, (1158849 / 125000000000)),
  (⟨(1 / 478), (11938 / 5706125), 477, true, 1194, true⟩, (315451 / 500000000000)),
  (⟨(11938 / 5706125), (5 / 2388), 477, true, 1194, false⟩, (11194009 / 1000000000000)),
  (⟨(5 / 2388), (2 / 955), 477, true, 1193, false⟩, (335721 / 125000000000)),
  (⟨(2 / 955), (994 / 474615), 477, false, 1193, true⟩, (529501 / 1000000000000)),
  (⟨(994 / 474615), (5 / 2386), 477, false, 1193, false⟩, (277613 / 40000000000)),
  (⟨(5 / 2386), (1 / 477), 477, false, 1192, false⟩, (887427 / 200000000000)),
  (⟨(1 / 477), (11918 / 5684645), 476, true, 1192, true⟩, (159981 / 250000000000)),
  (⟨(11918 / 5684645), (5 / 2384), 476, true, 1192, false⟩, (2756991 / 500000000000)),
  (⟨(5 / 2384), (2 / 953), 476, true, 1191, false⟩, (526117 / 62500000000)),
  (⟨(2 / 953), (2977 / 1418480), 476, false, 1191, true⟩, (268529 / 500000000000)),
  (⟨(2977 / 1418480), (5 / 2382), 476, false, 1191, false⟩, (517777 / 250000000000)),
  (⟨(5 / 2382), (1 / 476), 476, false, 1190, false⟩, (2337207 / 250000000000)),
  (⟨(1 / 476), (5944 / 2829225), 475, true, 1189, true⟩, (636217 / 1000000000000)),
  (⟨(5944 / 2829225), (5 / 2378), 475, true, 1189, false⟩, (5644157 / 500000000000)),
  (⟨(5 / 2378), (2 / 951), 475, true, 1188, false⟩, (1354203 / 500000000000)),
  (⟨(2 / 951), (5939 / 2823875), 475, false, 1188, true⟩, (266989 / 500000000000)),
  (⟨(5939 / 2823875), (5 / 2376), 475, false, 1188, false⟩, (6998839 / 1000000000000)),
  (⟨(5 / 2376), (1 / 475), 475, false, 1187, false⟩, (4474571 / 1000000000000)),
  (⟨(1 / 475), (989 / 469755), 474, true, 1187, true⟩, (322677 / 500000000000)),
  (⟨(989 / 469755), (5 / 2374), 474, true, 1187, false⟩, (347531 / 62500000000)),
  (⟨(5 / 2374), (2 / 949), 474, true, 1186, false⟩, (8488961 / 1000000000000)),
  (⟨(2 / 949), (5929 / 2813190), 474, false, 1186, true⟩, (541631 / 1000000000000)),
  (⟨(5929 / 2813190), (5 / 2372), 474, false, 1186, false⟩, (2088571 / 1000000000000)),
  (⟨(5 / 2372), (1 / 474), 474, false, 1185, false⟩, (4713927 / 500000000000)),
  (⟨(1 / 474), (3946 / 1870325), 473, true, 1184, true⟩, (401 / 625000000)),
  (⟨(3946 / 1870325), (5 / 2368), 473, true, 1184, false⟩, (1422977 / 125000000000)),
  (⟨(5 / 2368), (2 / 947), 473, true, 1183, false⟩, (682833 / 250000000000)),
  (⟨(2 / 947), (2957 / 1400080), 473, false, 1183, true⟩, (33657 / 62500000000)),
  (⟨(2957 / 1400080), (5 / 2366), 473, false, 1183, false⟩, (7058097 / 1000000000000)),
  (⟨(5 / 2366), (1 / 473), 473, false, 1182, false⟩, (4512483 / 1000000000000)),
  (⟨(1 / 473), (11818 / 5589675), 472, true, 1182, true⟩, (650853 / 1000000000000)),
  (⟨(11818 / 5589675), (5 / 2364), 472, true, 1182, false⟩, (2803801 / 500000000000)),
  (⟨(5 / 2364), (2 / 945), 472, true, 1181, false⟩, (4280477 / 500000000000)),
  (⟨(2 / 945), (123 / 58115), 472, false, 1181, true⟩, (546263 / 1000000000000)),
  (⟨(123 / 58115), (5 / 2362), 472, false, 1181, false⟩, (131641 / 62500000000)),
  (⟨(5 / 2362), (1 / 472), 472, false, 1180, false⟩, (9507887 / 1000000000000)),
  (⟨(1 / 472), (2947 / 1390925), 471, true, 1179, true⟩, (161763 / 250000000000)),
  (⟨(2947 / 1390925), (5 / 2358), 471, true, 1179, false⟩, (2296107 / 200000000000)),
  (⟨(5 / 2358), (2 / 943), 471, true, 1178, false⟩, (55091 / 20000000000)),
  (⟨(2 / 943), (1963 / 925515), 471, false, 1178, true⟩, (108621 / 200000000000)),
  (⟨(1963 / 925515), (5 / 2356), 471, false, 1178, false⟩, (711811 / 100000000000)),
  (⟨(5 / 2356), (1 / 471), 471, false, 1177, false⟩, (2275439 / 500000000000)),
  (⟨(1 / 471), (5884 / 2771245), 470, true, 1177, true⟩, (656423 / 1000000000000)),
  (⟨(5884 / 2771245), (5 / 2354), 470, true, 1177, false⟩, (1413827 / 250000000000)),
  (⟨(5 / 2354), (2 / 941), 470, true, 1176, false⟩, (2158467 / 250000000000)),
  (⟨(2 / 941), (5879 / 2765950), 470, false, 1176, true⟩, (275477 / 500000000000)),
  (⟨(5879 / 2765950), (5 / 2352), 470, false, 1176, false⟩, (2124167 / 1000000000000)),
  (⟨(5 / 2352), (1 / 470), 470, false, 1175, false⟩, (4794471 / 500000000000)),
  (⟨(1 / 470), (11738 / 5516625), 469, true, 1174, true⟩, (652573 / 1000000000000)),
  (⟨(11738 / 5516625), (5 / 2348), 469, true, 1174, false⟩, (11578491 / 1000000000000)),
  (⟨(5 / 2348), (2 / 939), 469, true, 1173, false⟩, (1389033 / 500000000000)),
  (⟨(2 / 939), (2932 / 1376515), 469, false, 1173, true⟩, (136939 / 250000000000))]

theorem fits : cappedChainFits (5 / 2454) cells := by
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

theorem endpoint : cappedChainEnd (5 / 2454) cells = (2932 / 1376515) := by rfl

theorem upper : cappedChainUpper cells = (557876601 / 1000000000000) := by
  norm_num [cappedChainUpper, cells]

theorem bound :
    IntervalIntegrable middleRankProfile MeasureTheory.volume ((5 / 2454) : ℝ) ((2932 / 1376515) : ℝ) ∧
    (∫ β in ((5 / 2454) : ℝ)..((2932 / 1376515) : ℝ), middleRankProfile β) ≤ ((557876601 / 1000000000000) : ℝ) := by
  have h := integrate_cappedChain fits
  rw [endpoint, upper] at h
  norm_num at h ⊢
  exact h

end Block01
end Zeta5.Certificate.ExtendedArithmetic
