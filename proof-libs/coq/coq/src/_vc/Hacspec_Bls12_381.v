(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
Require Import Hacspec_Lib.

Definition fp_canvas_t := nseq (int8) (48).
Definition fp_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Instance show_fp_t : Show (fp_t) := Build_Show (fp_t) (fun x => show (GZnZ.val _ x)).
Definition g_fp_t : G (fp_t) := @bindGen Z (fp_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_fp_t : Gen (fp_t) := Build_Gen fp_t g_fp_t.


Definition serialized_fp_t := nseq (uint8) (usize 48).

Definition array_fp_t := nseq (uint64) (usize 6).

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.
Instance show_scalar_t : Show (scalar_t) := Build_Show (scalar_t) (fun x => show (GZnZ.val _ x)).
Definition g_scalar_t : G (scalar_t) := @bindGen Z (scalar_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_scalar_t : Gen (scalar_t) := Build_Gen scalar_t g_scalar_t.


Notation "'g1_t'" := ((fp_t × fp_t × bool)) : hacspec_scope.
Instance show_g1_t : Show (g1_t) :=
Build_Show g1_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g1_t : G (g1_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g1_t : Gen (g1_t) := Build_Gen g1_t g_g1_t.


Notation "'fp2_t'" := ((fp_t × fp_t)) : hacspec_scope.
Instance show_fp2_t : Show (fp2_t) :=
Build_Show fp2_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp2_t : G (fp2_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  returnGen (x0,x1))).
Instance gen_fp2_t : Gen (fp2_t) := Build_Gen fp2_t g_fp2_t.


Notation "'g2_t'" := ((fp2_t × fp2_t × bool)) : hacspec_scope.
Instance show_g2_t : Show (g2_t) :=
Build_Show g2_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g2_t : G (g2_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g2_t : Gen (g2_t) := Build_Gen g2_t g_g2_t.


Notation "'fp6_t'" := ((fp2_t × fp2_t × fp2_t)) : hacspec_scope.
Instance show_fp6_t : Show (fp6_t) :=
Build_Show fp6_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_fp6_t : G (fp6_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : fp2_t =>
  returnGen (x0,x1,x2)))).
Instance gen_fp6_t : Gen (fp6_t) := Build_Gen fp6_t g_fp6_t.


Notation "'fp12_t'" := ((fp6_t × fp6_t)) : hacspec_scope.
Instance show_fp12_t : Show (fp12_t) :=
Build_Show fp12_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp12_t : G (fp12_t) :=
bindGen arbitrary (fun x0 : fp6_t =>
  bindGen arbitrary (fun x1 : fp6_t =>
  returnGen (x0,x1))).
Instance gen_fp12_t : Gen (fp12_t) := Build_Gen fp12_t g_fp12_t.


Definition fp2fromfp (n_1063 : fp_t) : fp2_t :=
  (n_1063, nat_mod_zero ).

Definition fp2zero  : fp2_t :=
  fp2fromfp (nat_mod_zero ).

Definition fp2neg (n_1064 : fp2_t) : fp2_t :=
  let '(n1_1065, n2_1066) :=
    n_1064 in 
  ((nat_mod_zero ) -% (n1_1065), (nat_mod_zero ) -% (n2_1066)).

Definition fp2add (n_1067 : fp2_t) (m_1068 : fp2_t) : fp2_t :=
  let '(n1_1069, n2_1070) :=
    n_1067 in 
  let '(m1_1071, m2_1072) :=
    m_1068 in 
  ((n1_1069) +% (m1_1071), (n2_1070) +% (m2_1072)).

Definition fp2sub (n_1073 : fp2_t) (m_1074 : fp2_t) : fp2_t :=
  fp2add (n_1073) (fp2neg (m_1074)).

Definition fp2mul (n_1075 : fp2_t) (m_1076 : fp2_t) : fp2_t :=
  let '(n1_1077, n2_1078) :=
    n_1075 in 
  let '(m1_1079, m2_1080) :=
    m_1076 in 
  let x1_1081 : fp_t :=
    ((n1_1077) *% (m1_1079)) -% ((n2_1078) *% (m2_1080)) in 
  let x2_1082 : fp_t :=
    ((n1_1077) *% (m2_1080)) +% ((n2_1078) *% (m1_1079)) in 
  (x1_1081, x2_1082).

Definition fp2inv (n_1083 : fp2_t) : fp2_t :=
  let '(n1_1084, n2_1085) :=
    n_1083 in 
  let t0_1086 : fp_t :=
    ((n1_1084) *% (n1_1084)) +% ((n2_1085) *% (n2_1085)) in 
  let t1_1087 : fp_t :=
    nat_mod_inv (t0_1086) in 
  let x1_1088 : fp_t :=
    (n1_1084) *% (t1_1087) in 
  let x2_1089 : fp_t :=
    (nat_mod_zero ) -% ((n2_1085) *% (t1_1087)) in 
  (x1_1088, x2_1089).

Definition fp2conjugate (n_1090 : fp2_t) : fp2_t :=
  let '(n1_1091, n2_1092) :=
    n_1090 in 
  (n1_1091, (nat_mod_zero ) -% (n2_1092)).

Definition fp6fromfp2 (n_1093 : fp2_t) : fp6_t :=
  (n_1093, fp2zero , fp2zero ).

Definition fp6zero  : fp6_t :=
  fp6fromfp2 (fp2zero ).

Definition fp6neg (n_1094 : fp6_t) : fp6_t :=
  let '(n1_1095, n2_1096, n3_1097) :=
    n_1094 in 
  (
    fp2sub (fp2zero ) (n1_1095),
    fp2sub (fp2zero ) (n2_1096),
    fp2sub (fp2zero ) (n3_1097)
  ).

Definition fp6add (n_1098 : fp6_t) (m_1099 : fp6_t) : fp6_t :=
  let '(n1_1100, n2_1101, n3_1102) :=
    n_1098 in 
  let '(m1_1103, m2_1104, m3_1105) :=
    m_1099 in 
  (
    fp2add (n1_1100) (m1_1103),
    fp2add (n2_1101) (m2_1104),
    fp2add (n3_1102) (m3_1105)
  ).

Definition fp6sub (n_1106 : fp6_t) (m_1107 : fp6_t) : fp6_t :=
  fp6add (n_1106) (fp6neg (m_1107)).

Definition fp6mul (n_1108 : fp6_t) (m_1109 : fp6_t) : fp6_t :=
  let '(n1_1110, n2_1111, n3_1112) :=
    n_1108 in 
  let '(m1_1113, m2_1114, m3_1115) :=
    m_1109 in 
  let eps_1116 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1117 : (fp_t × fp_t) :=
    fp2mul (n1_1110) (m1_1113) in 
  let t2_1118 : (fp_t × fp_t) :=
    fp2mul (n2_1111) (m2_1114) in 
  let t3_1119 : (fp_t × fp_t) :=
    fp2mul (n3_1112) (m3_1115) in 
  let t4_1120 : (fp_t × fp_t) :=
    fp2mul (fp2add (n2_1111) (n3_1112)) (fp2add (m2_1114) (m3_1115)) in 
  let t5_1121 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_1120) (t2_1118)) (t3_1119) in 
  let x_1122 : (fp_t × fp_t) :=
    fp2add (fp2mul (t5_1121) (eps_1116)) (t1_1117) in 
  let t4_1123 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_1110) (n2_1111)) (fp2add (m1_1113) (m2_1114)) in 
  let t5_1124 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_1123) (t1_1117)) (t2_1118) in 
  let y_1125 : (fp_t × fp_t) :=
    fp2add (t5_1124) (fp2mul (eps_1116) (t3_1119)) in 
  let t4_1126 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_1110) (n3_1112)) (fp2add (m1_1113) (m3_1115)) in 
  let t5_1127 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_1126) (t1_1117)) (t3_1119) in 
  let z_1128 : (fp_t × fp_t) :=
    fp2add (t5_1127) (t2_1118) in 
  (x_1122, y_1125, z_1128).

Definition fp6inv (n_1129 : fp6_t) : fp6_t :=
  let '(n1_1130, n2_1131, n3_1132) :=
    n_1129 in 
  let eps_1133 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1134 : (fp_t × fp_t) :=
    fp2mul (n1_1130) (n1_1130) in 
  let t2_1135 : (fp_t × fp_t) :=
    fp2mul (n2_1131) (n2_1131) in 
  let t3_1136 : (fp_t × fp_t) :=
    fp2mul (n3_1132) (n3_1132) in 
  let t4_1137 : (fp_t × fp_t) :=
    fp2mul (n1_1130) (n2_1131) in 
  let t5_1138 : (fp_t × fp_t) :=
    fp2mul (n1_1130) (n3_1132) in 
  let t6_1139 : (fp_t × fp_t) :=
    fp2mul (n2_1131) (n3_1132) in 
  let x0_1140 : (fp_t × fp_t) :=
    fp2sub (t1_1134) (fp2mul (eps_1133) (t6_1139)) in 
  let y0_1141 : (fp_t × fp_t) :=
    fp2sub (fp2mul (eps_1133) (t3_1136)) (t4_1137) in 
  let z0_1142 : (fp_t × fp_t) :=
    fp2sub (t2_1135) (t5_1138) in 
  let t0_1143 : (fp_t × fp_t) :=
    fp2mul (n1_1130) (x0_1140) in 
  let t0_1144 : (fp_t × fp_t) :=
    fp2add (t0_1143) (fp2mul (eps_1133) (fp2mul (n3_1132) (y0_1141))) in 
  let t0_1145 : (fp_t × fp_t) :=
    fp2add (t0_1144) (fp2mul (eps_1133) (fp2mul (n2_1131) (z0_1142))) in 
  let t0_1146 : (fp_t × fp_t) :=
    fp2inv (t0_1145) in 
  let x_1147 : (fp_t × fp_t) :=
    fp2mul (x0_1140) (t0_1146) in 
  let y_1148 : (fp_t × fp_t) :=
    fp2mul (y0_1141) (t0_1146) in 
  let z_1149 : (fp_t × fp_t) :=
    fp2mul (z0_1142) (t0_1146) in 
  (x_1147, y_1148, z_1149).

Definition fp12fromfp6 (n_1150 : fp6_t) : fp12_t :=
  (n_1150, fp6zero ).

Definition fp12neg (n_1151 : fp12_t) : fp12_t :=
  let '(n1_1152, n2_1153) :=
    n_1151 in 
  (fp6sub (fp6zero ) (n1_1152), fp6sub (fp6zero ) (n2_1153)).

Definition fp12add (n_1154 : fp12_t) (m_1155 : fp12_t) : fp12_t :=
  let '(n1_1156, n2_1157) :=
    n_1154 in 
  let '(m1_1158, m2_1159) :=
    m_1155 in 
  (fp6add (n1_1156) (m1_1158), fp6add (n2_1157) (m2_1159)).

Definition fp12sub (n_1160 : fp12_t) (m_1161 : fp12_t) : fp12_t :=
  fp12add (n_1160) (fp12neg (m_1161)).

Definition fp12mul (n_1162 : fp12_t) (m_1163 : fp12_t) : fp12_t :=
  let '(n1_1164, n2_1165) :=
    n_1162 in 
  let '(m1_1166, m2_1167) :=
    m_1163 in 
  let gamma_1168 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1169 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_1164) (m1_1166) in 
  let t2_1170 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_1165) (m2_1167) in 
  let x_1171 : (fp2_t × fp2_t × fp2_t) :=
    fp6add (t1_1169) (fp6mul (t2_1170) (gamma_1168)) in 
  let y_1172 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (fp6add (n1_1164) (n2_1165)) (fp6add (m1_1166) (m2_1167)) in 
  let y_1173 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (fp6sub (y_1172) (t1_1169)) (t2_1170) in 
  (x_1171, y_1173).

Definition fp12inv (n_1174 : fp12_t) : fp12_t :=
  let '(n1_1175, n2_1176) :=
    n_1174 in 
  let gamma_1177 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1178 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_1175) (n1_1175) in 
  let t2_1179 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_1176) (n2_1176) in 
  let t1_1180 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (t1_1178) (fp6mul (gamma_1177) (t2_1179)) in 
  let t2_1181 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (t1_1180) in 
  let x_1182 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_1175) (t2_1181) in 
  let y_1183 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (fp6mul (n2_1176) (t2_1181)) in 
  (x_1182, y_1183).

Definition fp12exp (n_1184 : fp12_t) (k_1185 : scalar_t) : fp12_t :=
  let c_1186 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let c_1186 :=
    foldi (usize 0) (usize 256) (fun i_1187 c_1186 =>
      let c_1186 :=
        fp12mul (c_1186) (c_1186) in 
      let '(c_1186) :=
        if nat_mod_bit (k_1185) ((usize 255) - (i_1187)):bool then (
          let c_1186 :=
            fp12mul (c_1186) (n_1184) in 
          (c_1186)) else ((c_1186)) in 
      (c_1186))
    c_1186 in 
  c_1186.

Definition fp12conjugate (n_1188 : fp12_t) : fp12_t :=
  let '(n1_1189, n2_1190) :=
    n_1188 in 
  (n1_1189, fp6neg (n2_1190)).

Definition fp12zero  : fp12_t :=
  fp12fromfp6 (fp6zero ).

Definition g1add_a (p_1191 : g1_t) (q_1192 : g1_t) : g1_t :=
  let '(x1_1193, y1_1194, _) :=
    p_1191 in 
  let '(x2_1195, y2_1196, _) :=
    q_1192 in 
  let x_diff_1197 : fp_t :=
    (x2_1195) -% (x1_1193) in 
  let y_diff_1198 : fp_t :=
    (y2_1196) -% (y1_1194) in 
  let xovery_1199 : fp_t :=
    (y_diff_1198) *% (nat_mod_inv (x_diff_1197)) in 
  let x3_1200 : fp_t :=
    ((nat_mod_exp (xovery_1199) (@repr WORDSIZE32 2)) -% (x1_1193)) -% (
      x2_1195) in 
  let y3_1201 : fp_t :=
    ((xovery_1199) *% ((x1_1193) -% (x3_1200))) -% (y1_1194) in 
  (x3_1200, y3_1201, false).

Definition g1double_a (p_1202 : g1_t) : g1_t :=
  let '(x1_1203, y1_1204, _) :=
    p_1202 in 
  let x12_1205 : fp_t :=
    nat_mod_exp (x1_1203) (@repr WORDSIZE32 2) in 
  let xovery_1206 : fp_t :=
    ((nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t) *% (x12_1205)) *% (nat_mod_inv ((
          nat_mod_two ) *% (y1_1204))) in 
  let x3_1207 : fp_t :=
    (nat_mod_exp (xovery_1206) (@repr WORDSIZE32 2)) -% ((nat_mod_two ) *% (
        x1_1203)) in 
  let y3_1208 : fp_t :=
    ((xovery_1206) *% ((x1_1203) -% (x3_1207))) -% (y1_1204) in 
  (x3_1207, y3_1208, false).

Definition g1double (p_1209 : g1_t) : g1_t :=
  let '(x1_1210, y1_1211, inf1_1212) :=
    p_1209 in 
  (if (((y1_1211) !=.? (nat_mod_zero )) && (negb (inf1_1212))):bool then (
      g1double_a (p_1209)) else ((nat_mod_zero , nat_mod_zero , true))).

Definition g1add (p_1213 : g1_t) (q_1214 : g1_t) : g1_t :=
  let '(x1_1215, y1_1216, inf1_1217) :=
    p_1213 in 
  let '(x2_1218, y2_1219, inf2_1220) :=
    q_1214 in 
  (if (inf1_1217):bool then (q_1214) else ((if (inf2_1220):bool then (
          p_1213) else ((if ((p_1213) =.? (q_1214)):bool then (g1double (
                p_1213)) else ((if (negb (((x1_1215) =.? (x2_1218)) && ((
                        y1_1216) =.? ((nat_mod_zero ) -% (
                          y2_1219))))):bool then (g1add_a (p_1213) (
                    q_1214)) else ((nat_mod_zero , nat_mod_zero , true))))))))).

Definition g1mul (m_1221 : scalar_t) (p_1222 : g1_t) : g1_t :=
  let t_1223 : (fp_t × fp_t × bool) :=
    (nat_mod_zero , nat_mod_zero , true) in 
  let t_1223 :=
    foldi (usize 0) (usize 256) (fun i_1224 t_1223 =>
      let t_1223 :=
        g1double (t_1223) in 
      let '(t_1223) :=
        if nat_mod_bit (m_1221) ((usize 255) - (i_1224)):bool then (
          let t_1223 :=
            g1add (t_1223) (p_1222) in 
          (t_1223)) else ((t_1223)) in 
      (t_1223))
    t_1223 in 
  t_1223.

Definition g1neg (p_1225 : g1_t) : g1_t :=
  let '(x_1226, y_1227, inf_1228) :=
    p_1225 in 
  (x_1226, (nat_mod_zero ) -% (y_1227), inf_1228).

Definition g2add_a (p_1229 : g2_t) (q_1230 : g2_t) : g2_t :=
  let '(x1_1231, y1_1232, _) :=
    p_1229 in 
  let '(x2_1233, y2_1234, _) :=
    q_1230 in 
  let x_diff_1235 : (fp_t × fp_t) :=
    fp2sub (x2_1233) (x1_1231) in 
  let y_diff_1236 : (fp_t × fp_t) :=
    fp2sub (y2_1234) (y1_1232) in 
  let xovery_1237 : (fp_t × fp_t) :=
    fp2mul (y_diff_1236) (fp2inv (x_diff_1235)) in 
  let t1_1238 : (fp_t × fp_t) :=
    fp2mul (xovery_1237) (xovery_1237) in 
  let t2_1239 : (fp_t × fp_t) :=
    fp2sub (t1_1238) (x1_1231) in 
  let x3_1240 : (fp_t × fp_t) :=
    fp2sub (t2_1239) (x2_1233) in 
  let t1_1241 : (fp_t × fp_t) :=
    fp2sub (x1_1231) (x3_1240) in 
  let t2_1242 : (fp_t × fp_t) :=
    fp2mul (xovery_1237) (t1_1241) in 
  let y3_1243 : (fp_t × fp_t) :=
    fp2sub (t2_1242) (y1_1232) in 
  (x3_1240, y3_1243, false).

Definition g2double_a (p_1244 : g2_t) : g2_t :=
  let '(x1_1245, y1_1246, _) :=
    p_1244 in 
  let x12_1247 : (fp_t × fp_t) :=
    fp2mul (x1_1245) (x1_1245) in 
  let t1_1248 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (x12_1247) in 
  let t2_1249 : (fp_t × fp_t) :=
    fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (y1_1246)) in 
  let xovery_1250 : (fp_t × fp_t) :=
    fp2mul (t1_1248) (t2_1249) in 
  let t1_1251 : (fp_t × fp_t) :=
    fp2mul (xovery_1250) (xovery_1250) in 
  let t2_1252 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_two )) (x1_1245) in 
  let x3_1253 : (fp_t × fp_t) :=
    fp2sub (t1_1251) (t2_1252) in 
  let t1_1254 : (fp_t × fp_t) :=
    fp2sub (x1_1245) (x3_1253) in 
  let t2_1255 : (fp_t × fp_t) :=
    fp2mul (xovery_1250) (t1_1254) in 
  let y3_1256 : (fp_t × fp_t) :=
    fp2sub (t2_1255) (y1_1246) in 
  (x3_1253, y3_1256, false).

Definition g2double (p_1257 : g2_t) : g2_t :=
  let '(x1_1258, y1_1259, inf1_1260) :=
    p_1257 in 
  (if (((y1_1259) !=.? (fp2zero )) && (negb (inf1_1260))):bool then (
      g2double_a (p_1257)) else ((fp2zero , fp2zero , true))).

Definition g2add (p_1261 : g2_t) (q_1262 : g2_t) : g2_t :=
  let '(x1_1263, y1_1264, inf1_1265) :=
    p_1261 in 
  let '(x2_1266, y2_1267, inf2_1268) :=
    q_1262 in 
  (if (inf1_1265):bool then (q_1262) else ((if (inf2_1268):bool then (
          p_1261) else ((if ((p_1261) =.? (q_1262)):bool then (g2double (
                p_1261)) else ((if (negb (((x1_1263) =.? (x2_1266)) && ((
                        y1_1264) =.? (fp2neg (y2_1267))))):bool then (g2add_a (
                    p_1261) (q_1262)) else ((fp2zero , fp2zero , true))))))))).

Definition g2mul (m_1269 : scalar_t) (p_1270 : g2_t) : g2_t :=
  let t_1271 : (fp2_t × fp2_t × bool) :=
    (fp2zero , fp2zero , true) in 
  let t_1271 :=
    foldi (usize 0) (usize 256) (fun i_1272 t_1271 =>
      let t_1271 :=
        g2double (t_1271) in 
      let '(t_1271) :=
        if nat_mod_bit (m_1269) ((usize 255) - (i_1272)):bool then (
          let t_1271 :=
            g2add (t_1271) (p_1270) in 
          (t_1271)) else ((t_1271)) in 
      (t_1271))
    t_1271 in 
  t_1271.

Definition g2neg (p_1273 : g2_t) : g2_t :=
  let '(x_1274, y_1275, inf_1276) :=
    p_1273 in 
  (x_1274, fp2neg (y_1275), inf_1276).

Definition twist (p_1277 : g1_t) : (fp12_t × fp12_t) :=
  let '(p0_1278, p1_1279, _) :=
    p_1277 in 
  let x_1280 : ((fp2_t × fp2_t × fp2_t) × fp6_t) :=
    ((fp2zero , fp2fromfp (p0_1278), fp2zero ), fp6zero ) in 
  let y_1281 : (fp6_t × (fp2_t × fp2_t × fp2_t)) :=
    (fp6zero , (fp2zero , fp2fromfp (p1_1279), fp2zero )) in 
  (x_1280, y_1281).

Definition line_double_p (r_1282 : g2_t) (p_1283 : g1_t) : fp12_t :=
  let '(r0_1284, r1_1285, _) :=
    r_1282 in 
  let a_1286 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (fp2mul (r0_1284) (r0_1284)) in 
  let a_1287 : (fp_t × fp_t) :=
    fp2mul (a_1286) (fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (r1_1285))) in 
  let b_1288 : (fp_t × fp_t) :=
    fp2sub (r1_1285) (fp2mul (a_1287) (r0_1284)) in 
  let a_1289 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1287)) in 
  let b_1290 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1288)) in 
  let '(x_1291, y_1292) :=
    twist (p_1283) in 
  fp12neg (fp12sub (fp12sub (y_1292) (fp12mul (a_1289) (x_1291))) (b_1290)).

Definition line_add_p
  (r_1293 : g2_t)
  (q_1294 : g2_t)
  (p_1295 : g1_t)
  : fp12_t :=
  let '(r0_1296, r1_1297, _) :=
    r_1293 in 
  let '(q0_1298, q1_1299, _) :=
    q_1294 in 
  let a_1300 : (fp_t × fp_t) :=
    fp2mul (fp2sub (q1_1299) (r1_1297)) (fp2inv (fp2sub (q0_1298) (
          r0_1296))) in 
  let b_1301 : (fp_t × fp_t) :=
    fp2sub (r1_1297) (fp2mul (a_1300) (r0_1296)) in 
  let a_1302 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1300)) in 
  let b_1303 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1301)) in 
  let '(x_1304, y_1305) :=
    twist (p_1295) in 
  fp12neg (fp12sub (fp12sub (y_1305) (fp12mul (a_1302) (x_1304))) (b_1303)).

Definition frobenius (f_1306 : fp12_t) : fp12_t :=
  let '((g0_1307, g1_1308, g2_1309), (h0_1310, h1_1311, h2_1312)) :=
    f_1306 in 
  let t1_1313 : (fp_t × fp_t) :=
    fp2conjugate (g0_1307) in 
  let t2_1314 : (fp_t × fp_t) :=
    fp2conjugate (h0_1310) in 
  let t3_1315 : (fp_t × fp_t) :=
    fp2conjugate (g1_1308) in 
  let t4_1316 : (fp_t × fp_t) :=
    fp2conjugate (h1_1311) in 
  let t5_1317 : (fp_t × fp_t) :=
    fp2conjugate (g2_1309) in 
  let t6_1318 : (fp_t × fp_t) :=
    fp2conjugate (h2_1312) in 
  let c1_1319 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 10162220747404304312) : int64;
          secret (@repr WORDSIZE64 17761815663483519293) : int64;
          secret (@repr WORDSIZE64 8873291758750579140) : int64;
          secret (@repr WORDSIZE64 1141103941765652303) : int64;
          secret (@repr WORDSIZE64 13993175198059990303) : int64;
          secret (@repr WORDSIZE64 1802798568193066599) : int64
        ] in  l) in 
  let c1_1320 : seq uint8 :=
    array_to_le_bytes (c1_1319) in 
  let c1_1321 : fp_t :=
    nat_mod_from_byte_seq_le (c1_1320) : fp_t in 
  let c2_1322 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 3240210268673559283) : int64;
          secret (@repr WORDSIZE64 2895069921743240898) : int64;
          secret (@repr WORDSIZE64 17009126888523054175) : int64;
          secret (@repr WORDSIZE64 6098234018649060207) : int64;
          secret (@repr WORDSIZE64 9865672654120263608) : int64;
          secret (@repr WORDSIZE64 71000049454473266) : int64
        ] in  l) in 
  let c2_1323 : seq uint8 :=
    array_to_le_bytes (c2_1322) in 
  let c2_1324 : fp_t :=
    nat_mod_from_byte_seq_le (c2_1323) : fp_t in 
  let gamma11_1325 : (fp_t × fp_t) :=
    (c1_1321, c2_1324) in 
  let gamma12_1326 : (fp_t × fp_t) :=
    fp2mul (gamma11_1325) (gamma11_1325) in 
  let gamma13_1327 : (fp_t × fp_t) :=
    fp2mul (gamma12_1326) (gamma11_1325) in 
  let gamma14_1328 : (fp_t × fp_t) :=
    fp2mul (gamma13_1327) (gamma11_1325) in 
  let gamma15_1329 : (fp_t × fp_t) :=
    fp2mul (gamma14_1328) (gamma11_1325) in 
  let t2_1330 : (fp_t × fp_t) :=
    fp2mul (t2_1314) (gamma11_1325) in 
  let t3_1331 : (fp_t × fp_t) :=
    fp2mul (t3_1315) (gamma12_1326) in 
  let t4_1332 : (fp_t × fp_t) :=
    fp2mul (t4_1316) (gamma13_1327) in 
  let t5_1333 : (fp_t × fp_t) :=
    fp2mul (t5_1317) (gamma14_1328) in 
  let t6_1334 : (fp_t × fp_t) :=
    fp2mul (t6_1318) (gamma15_1329) in 
  ((t1_1313, t3_1331, t5_1333), (t2_1330, t4_1332, t6_1334)).

Definition final_exponentiation (f_1335 : fp12_t) : fp12_t :=
  let fp6_1336 : (fp6_t × fp6_t) :=
    fp12conjugate (f_1335) in 
  let finv_1337 : (fp6_t × fp6_t) :=
    fp12inv (f_1335) in 
  let fp6_1_1338 : (fp6_t × fp6_t) :=
    fp12mul (fp6_1336) (finv_1337) in 
  let fp8_1339 : (fp6_t × fp6_t) :=
    frobenius (frobenius (fp6_1_1338)) in 
  let f_1340 : (fp6_t × fp6_t) :=
    fp12mul (fp8_1339) (fp6_1_1338) in 
  let u_1341 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let t0_1342 : (fp6_t × fp6_t) :=
    fp12mul (f_1340) (f_1340) in 
  let t1_1343 : (fp6_t × fp6_t) :=
    fp12exp (t0_1342) (u_1341) in 
  let t1_1344 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1343) in 
  let t2_1345 : (fp6_t × fp6_t) :=
    fp12exp (t1_1344) ((u_1341) /% (nat_mod_two )) in 
  let t2_1346 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_1345) in 
  let t3_1347 : (fp6_t × fp6_t) :=
    fp12conjugate (f_1340) in 
  let t1_1348 : (fp6_t × fp6_t) :=
    fp12mul (t3_1347) (t1_1344) in 
  let t1_1349 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1348) in 
  let t1_1350 : (fp6_t × fp6_t) :=
    fp12mul (t1_1349) (t2_1346) in 
  let t2_1351 : (fp6_t × fp6_t) :=
    fp12exp (t1_1350) (u_1341) in 
  let t2_1352 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_1351) in 
  let t3_1353 : (fp6_t × fp6_t) :=
    fp12exp (t2_1352) (u_1341) in 
  let t3_1354 : (fp6_t × fp6_t) :=
    fp12conjugate (t3_1353) in 
  let t1_1355 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1350) in 
  let t3_1356 : (fp6_t × fp6_t) :=
    fp12mul (t1_1355) (t3_1354) in 
  let t1_1357 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1355) in 
  let t1_1358 : (fp6_t × fp6_t) :=
    frobenius (frobenius (frobenius (t1_1357))) in 
  let t2_1359 : (fp6_t × fp6_t) :=
    frobenius (frobenius (t2_1352)) in 
  let t1_1360 : (fp6_t × fp6_t) :=
    fp12mul (t1_1358) (t2_1359) in 
  let t2_1361 : (fp6_t × fp6_t) :=
    fp12exp (t3_1356) (u_1341) in 
  let t2_1362 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_1361) in 
  let t2_1363 : (fp6_t × fp6_t) :=
    fp12mul (t2_1362) (t0_1342) in 
  let t2_1364 : (fp6_t × fp6_t) :=
    fp12mul (t2_1363) (f_1340) in 
  let t1_1365 : (fp6_t × fp6_t) :=
    fp12mul (t1_1360) (t2_1364) in 
  let t2_1366 : (fp6_t × fp6_t) :=
    frobenius (t3_1356) in 
  let t1_1367 : (fp6_t × fp6_t) :=
    fp12mul (t1_1365) (t2_1366) in 
  t1_1367.

Definition pairing (p_1368 : g1_t) (q_1369 : g2_t) : fp12_t :=
  let t_1370 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let r_1371 : (fp2_t × fp2_t × bool) :=
    q_1369 in 
  let f_1372 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let '(r_1371, f_1372) :=
    foldi (usize 1) (usize 64) (fun i_1373 '(r_1371, f_1372) =>
      let lrr_1374 : (fp6_t × fp6_t) :=
        line_double_p (r_1371) (p_1368) in 
      let r_1371 :=
        g2double (r_1371) in 
      let f_1372 :=
        fp12mul (fp12mul (f_1372) (f_1372)) (lrr_1374) in 
      let '(r_1371, f_1372) :=
        if nat_mod_bit (t_1370) (((usize 64) - (i_1373)) - (
            usize 1)):bool then (let lrq_1375 : (fp6_t × fp6_t) :=
            line_add_p (r_1371) (q_1369) (p_1368) in 
          let r_1371 :=
            g2add (r_1371) (q_1369) in 
          let f_1372 :=
            fp12mul (f_1372) (lrq_1375) in 
          (r_1371, f_1372)) else ((r_1371, f_1372)) in 
      (r_1371, f_1372))
    (r_1371, f_1372) in 
  final_exponentiation (fp12conjugate (f_1372)).

Definition test_fp2_prop_add_neg (a_1376 : fp2_t) : bool :=
  let b_1377 : (fp_t × fp_t) :=
    fp2neg (a_1376) in 
  (fp2fromfp (nat_mod_zero )) =.? (fp2add (a_1376) (b_1377)).
QuickChick (forAll g_fp2_t (fun a_1376 : fp2_t =>test_fp2_prop_add_neg a_1376)).


Definition test_fp2_prop_mul_inv (a_1378 : fp2_t) : bool :=
  let b_1379 : (fp_t × fp_t) :=
    fp2inv (a_1378) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul (a_1378) (b_1379)).
QuickChick (forAll g_fp2_t (fun a_1378 : fp2_t =>test_fp2_prop_mul_inv a_1378)).


Definition test_extraction_issue  : bool :=
  let b_1380 : (fp_t × fp_t) :=
    fp2inv ((nat_mod_one , nat_mod_one )) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul ((nat_mod_one , nat_mod_one )) (
      b_1380)).
QuickChick (test_extraction_issue).


Definition test_fp6_prop_mul_inv (a_1381 : fp6_t) : bool :=
  let b_1382 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (a_1381) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_one ))) =.? (fp6mul (a_1381) (b_1382)).
QuickChick (forAll g_fp6_t (fun a_1381 : fp6_t =>test_fp6_prop_mul_inv a_1381)).


Definition test_fp6_prop_add_neg (a_1383 : fp6_t) : bool :=
  let b_1384 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (a_1383) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_zero ))) =.? (fp6add (a_1383) (b_1384)).
QuickChick (forAll g_fp6_t (fun a_1383 : fp6_t =>test_fp6_prop_add_neg a_1383)).


Definition test_fp12_prop_add_neg (a_1385 : fp12_t) : bool :=
  let b_1386 : (fp6_t × fp6_t) :=
    fp12neg (a_1385) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (a_1385) (
      b_1386)).
QuickChick (
  forAll g_fp12_t (fun a_1385 : fp12_t =>test_fp12_prop_add_neg a_1385)).


Definition test_fp12_prop_mul_inv (a_1387 : fp12_t) : bool :=
  let b_1388 : (fp6_t × fp6_t) :=
    fp12inv (a_1387) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (a_1387) (
      b_1388)).
QuickChick (
  forAll g_fp12_t (fun a_1387 : fp12_t =>test_fp12_prop_mul_inv a_1387)).


