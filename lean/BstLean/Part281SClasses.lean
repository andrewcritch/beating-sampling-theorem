import BstLean.Part281Parameters
import BstLean.Part281UniformS

namespace BstLean.Part281.TI
open BstLean.Part264b
open Real Set BstLean.Part182 BstLean.Part255

def SConditions {n : ℕ} (c ks : ℝ) : Prop :=
  0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧
  s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧ s3c1 n 46 c < 1 ∧
  0 ≤ s3Cpa n c - s3r1 n 46 ∧
  s3e0 n 46 ≤ (s3Cpa n c - s3r1 n 46) / s3ap n 46 ∧
  s3nks n 46 (√23/n) c ≤ n * ks

noncomputable def sNode (j : ℕ) : ℝ := (69 + j) / 200
noncomputable def sCap : ℕ → ℝ
  | 0 => (48789/250000)
  | 1 => (192883/1000000)
  | 2 => (11911/62500)
  | 3 => (94119/500000)
  | 4 => (92933/500000)
  | 5 => (183461/1000000)
  | 6 => (90511/500000)
  | 7 => (178549/1000000)
  | 8 => (88021/500000)
  | 9 => (347/2000)
  | 10 => (170923/1000000)
  | 11 => (16831/100000)
  | 12 => (82831/500000)
  | 13 => (162977/1000000)
  | 14 => (2504/15625)
  | 15 => (157497/1000000)
  | 16 => (154701/1000000)
  | 17 => (151867/1000000)
  | 18 => (74497/500000)
  | 19 => (146083/1000000)
  | 20 => (35783/250000)
  | 21 => (8773/62500)
  | 22 => (17289/125000)
  | 23 => (68117/500000)
  | 24 => (67067/500000)
  | 25 => (33003/250000)
  | 26 => (129867/1000000)
  | 27 => (1277/10000)
  | 28 => (125509/1000000)
  | 29 => (24659/200000)
  | 30 => (60529/500000)
  | 31 => (118797/1000000)
  | 32 => (3641/31250)
  | 33 => (57101/500000)
  | 34 => (27967/250000)
  | 35 => (27377/250000)
  | 36 => (26781/250000)
  | 37 => (52357/500000)
  | 38 => (102279/1000000)
  | 39 => (99817/1000000)
  | 40 => (97329/1000000)
  | 41 => (47407/500000)
  | 42 => (3027/31250)
  | 43 => (50573/500000)
  | 44 => (105473/1000000)
  | 45 => (54923/500000)
  | 46 => (57133/500000)
  | 47 => (118733/1000000)
  | 48 => (123249/1000000)
  | 49 => (127813/1000000)
  | 50 => (132427/1000000)
  | 51 => (34273/250000)
  | 52 => (8863/62500)
  | 53 => (9161/62500)
  | 54 => (151397/1000000)
  | 55 => (9767/62500)
  | 56 => (161201/1000000)
  | 57 => (83093/500000)
  | 58 => (42807/250000)
  | 59 => (176327/1000000)
  | 60 => (45371/250000)
  | 61 => (93351/500000)
  | 62 => (9599/50000)
  | 63 => (197319/1000000)
  | 64 => (101361/500000)
  | 65 => (208189/1000000)
  | 66 => (106861/500000)
  | 67 => (219321/1000000)
  | 68 => (56247/250000)
  | _ => 0

theorem sGrid {n : ℕ} (hn : 11883 ≤ n) (j : Fin 69) {c : ℝ} (hc : B (sNode j.val) (sNode (j.val+1)) c) :
    SConditions (n := n) c (sCap j.val) := by
  match j with
  | ⟨0, _⟩ =>
    have hc' : B (69 / 200) (7 / 20) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS0 hn hc'
  | ⟨1, _⟩ =>
    have hc' : B (7 / 20) (71 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS1 hn hc'
  | ⟨2, _⟩ =>
    have hc' : B (71 / 200) (9 / 25) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS2 hn hc'
  | ⟨3, _⟩ =>
    have hc' : B (9 / 25) (73 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS3 hn hc'
  | ⟨4, _⟩ =>
    have hc' : B (73 / 200) (37 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS4 hn hc'
  | ⟨5, _⟩ =>
    have hc' : B (37 / 100) (3 / 8) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS5 hn hc'
  | ⟨6, _⟩ =>
    have hc' : B (3 / 8) (19 / 50) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS6 hn hc'
  | ⟨7, _⟩ =>
    have hc' : B (19 / 50) (77 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS7 hn hc'
  | ⟨8, _⟩ =>
    have hc' : B (77 / 200) (39 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS8 hn hc'
  | ⟨9, _⟩ =>
    have hc' : B (39 / 100) (79 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS9 hn hc'
  | ⟨10, _⟩ =>
    have hc' : B (79 / 200) (2 / 5) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS10 hn hc'
  | ⟨11, _⟩ =>
    have hc' : B (2 / 5) (81 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS11 hn hc'
  | ⟨12, _⟩ =>
    have hc' : B (81 / 200) (41 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS12 hn hc'
  | ⟨13, _⟩ =>
    have hc' : B (41 / 100) (83 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS13 hn hc'
  | ⟨14, _⟩ =>
    have hc' : B (83 / 200) (21 / 50) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS14 hn hc'
  | ⟨15, _⟩ =>
    have hc' : B (21 / 50) (17 / 40) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS15 hn hc'
  | ⟨16, _⟩ =>
    have hc' : B (17 / 40) (43 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS16 hn hc'
  | ⟨17, _⟩ =>
    have hc' : B (43 / 100) (87 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS17 hn hc'
  | ⟨18, _⟩ =>
    have hc' : B (87 / 200) (11 / 25) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS18 hn hc'
  | ⟨19, _⟩ =>
    have hc' : B (11 / 25) (89 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS19 hn hc'
  | ⟨20, _⟩ =>
    have hc' : B (89 / 200) (9 / 20) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS20 hn hc'
  | ⟨21, _⟩ =>
    have hc' : B (9 / 20) (91 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS21 hn hc'
  | ⟨22, _⟩ =>
    have hc' : B (91 / 200) (23 / 50) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS22 hn hc'
  | ⟨23, _⟩ =>
    have hc' : B (23 / 50) (93 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS23 hn hc'
  | ⟨24, _⟩ =>
    have hc' : B (93 / 200) (47 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS24 hn hc'
  | ⟨25, _⟩ =>
    have hc' : B (47 / 100) (19 / 40) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS25 hn hc'
  | ⟨26, _⟩ =>
    have hc' : B (19 / 40) (12 / 25) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS26 hn hc'
  | ⟨27, _⟩ =>
    have hc' : B (12 / 25) (97 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS27 hn hc'
  | ⟨28, _⟩ =>
    have hc' : B (97 / 200) (49 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS28 hn hc'
  | ⟨29, _⟩ =>
    have hc' : B (49 / 100) (99 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS29 hn hc'
  | ⟨30, _⟩ =>
    have hc' : B (99 / 200) (1 / 2) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS30 hn hc'
  | ⟨31, _⟩ =>
    have hc' : B (1 / 2) (101 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS31 hn hc'
  | ⟨32, _⟩ =>
    have hc' : B (101 / 200) (51 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS32 hn hc'
  | ⟨33, _⟩ =>
    have hc' : B (51 / 100) (103 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS33 hn hc'
  | ⟨34, _⟩ =>
    have hc' : B (103 / 200) (13 / 25) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS34 hn hc'
  | ⟨35, _⟩ =>
    have hc' : B (13 / 25) (21 / 40) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS35 hn hc'
  | ⟨36, _⟩ =>
    have hc' : B (21 / 40) (53 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS36 hn hc'
  | ⟨37, _⟩ =>
    have hc' : B (53 / 100) (107 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS37 hn hc'
  | ⟨38, _⟩ =>
    have hc' : B (107 / 200) (27 / 50) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS38 hn hc'
  | ⟨39, _⟩ =>
    have hc' : B (27 / 50) (109 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS39 hn hc'
  | ⟨40, _⟩ =>
    have hc' : B (109 / 200) (11 / 20) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS40 hn hc'
  | ⟨41, _⟩ =>
    have hc' : B (11 / 20) (111 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS41 hn hc'
  | ⟨42, _⟩ =>
    have hc' : B (111 / 200) (14 / 25) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS42 hn hc'
  | ⟨43, _⟩ =>
    have hc' : B (14 / 25) (113 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS43 hn hc'
  | ⟨44, _⟩ =>
    have hc' : B (113 / 200) (57 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS44 hn hc'
  | ⟨45, _⟩ =>
    have hc' : B (57 / 100) (23 / 40) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS45 hn hc'
  | ⟨46, _⟩ =>
    have hc' : B (23 / 40) (29 / 50) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS46 hn hc'
  | ⟨47, _⟩ =>
    have hc' : B (29 / 50) (117 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS47 hn hc'
  | ⟨48, _⟩ =>
    have hc' : B (117 / 200) (59 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS48 hn hc'
  | ⟨49, _⟩ =>
    have hc' : B (59 / 100) (119 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS49 hn hc'
  | ⟨50, _⟩ =>
    have hc' : B (119 / 200) (3 / 5) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS50 hn hc'
  | ⟨51, _⟩ =>
    have hc' : B (3 / 5) (121 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS51 hn hc'
  | ⟨52, _⟩ =>
    have hc' : B (121 / 200) (61 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS52 hn hc'
  | ⟨53, _⟩ =>
    have hc' : B (61 / 100) (123 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS53 hn hc'
  | ⟨54, _⟩ =>
    have hc' : B (123 / 200) (31 / 50) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS54 hn hc'
  | ⟨55, _⟩ =>
    have hc' : B (31 / 50) (5 / 8) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS55 hn hc'
  | ⟨56, _⟩ =>
    have hc' : B (5 / 8) (63 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS56 hn hc'
  | ⟨57, _⟩ =>
    have hc' : B (63 / 100) (127 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS57 hn hc'
  | ⟨58, _⟩ =>
    have hc' : B (127 / 200) (16 / 25) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS58 hn hc'
  | ⟨59, _⟩ =>
    have hc' : B (16 / 25) (129 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS59 hn hc'
  | ⟨60, _⟩ =>
    have hc' : B (129 / 200) (13 / 20) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS60 hn hc'
  | ⟨61, _⟩ =>
    have hc' : B (13 / 20) (131 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS61 hn hc'
  | ⟨62, _⟩ =>
    have hc' : B (131 / 200) (33 / 50) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS62 hn hc'
  | ⟨63, _⟩ =>
    have hc' : B (33 / 50) (133 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS63 hn hc'
  | ⟨64, _⟩ =>
    have hc' : B (133 / 200) (67 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS64 hn hc'
  | ⟨65, _⟩ =>
    have hc' : B (67 / 100) (27 / 40) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS65 hn hc'
  | ⟨66, _⟩ =>
    have hc' : B (27 / 40) (17 / 25) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS66 hn hc'
  | ⟨67, _⟩ =>
    have hc' : B (17 / 25) (137 / 200) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS67 hn hc'
  | ⟨68, _⟩ =>
    have hc' : B (137 / 200) (69 / 100) c := by
      convert hc using 1 <;> norm_num [sNode]
    exact uniformS68 hn hc'
  | ⟨j + 69, h⟩ => exact False.elim (by omega)

theorem sStepUp41 : sCap 41 ≤ sCap 42 := by
  norm_num [sCap]

theorem sStepUp42 : sCap 42 ≤ sCap 43 := by
  norm_num [sCap]

theorem sStepUp43 : sCap 43 ≤ sCap 44 := by
  norm_num [sCap]

theorem sStepUp44 : sCap 44 ≤ sCap 45 := by
  norm_num [sCap]

theorem sStepUp45 : sCap 45 ≤ sCap 46 := by
  norm_num [sCap]

theorem sStepUp46 : sCap 46 ≤ sCap 47 := by
  norm_num [sCap]

theorem sStepUp47 : sCap 47 ≤ sCap 48 := by
  norm_num [sCap]

theorem sStepUp48 : sCap 48 ≤ sCap 49 := by
  norm_num [sCap]

theorem sStepUp49 : sCap 49 ≤ sCap 50 := by
  norm_num [sCap]

theorem sStepUp50 : sCap 50 ≤ sCap 51 := by
  norm_num [sCap]

theorem sStepUp51 : sCap 51 ≤ sCap 52 := by
  norm_num [sCap]

theorem sStepUp52 : sCap 52 ≤ sCap 53 := by
  norm_num [sCap]

theorem sStepUp53 : sCap 53 ≤ sCap 54 := by
  norm_num [sCap]

theorem sStepUp54 : sCap 54 ≤ sCap 55 := by
  norm_num [sCap]

theorem sStepUp55 : sCap 55 ≤ sCap 56 := by
  norm_num [sCap]

theorem sStepUp56 : sCap 56 ≤ sCap 57 := by
  norm_num [sCap]

theorem sStepUp57 : sCap 57 ≤ sCap 58 := by
  norm_num [sCap]

theorem sStepUp58 : sCap 58 ≤ sCap 59 := by
  norm_num [sCap]

theorem sStepUp59 : sCap 59 ≤ sCap 60 := by
  norm_num [sCap]

theorem sStepUp60 : sCap 60 ≤ sCap 61 := by
  norm_num [sCap]

theorem sStepUp61 : sCap 61 ≤ sCap 62 := by
  norm_num [sCap]

theorem sStepUp62 : sCap 62 ≤ sCap 63 := by
  norm_num [sCap]

theorem sStepUp63 : sCap 63 ≤ sCap 64 := by
  norm_num [sCap]

theorem sStepUp64 : sCap 64 ≤ sCap 65 := by
  norm_num [sCap]

theorem sStepUp65 : sCap 65 ≤ sCap 66 := by
  norm_num [sCap]

theorem sStepUp66 : sCap 66 ≤ sCap 67 := by
  norm_num [sCap]

theorem sStepUp67 : sCap 67 ≤ sCap 68 := by
  norm_num [sCap]

theorem sStepUpFin (k : Fin 27) : sCap (k.val+41) ≤ sCap (k.val+42) := by
  match k with
  | ⟨0,_⟩ => exact sStepUp41
  | ⟨1,_⟩ => exact sStepUp42
  | ⟨2,_⟩ => exact sStepUp43
  | ⟨3,_⟩ => exact sStepUp44
  | ⟨4,_⟩ => exact sStepUp45
  | ⟨5,_⟩ => exact sStepUp46
  | ⟨6,_⟩ => exact sStepUp47
  | ⟨7,_⟩ => exact sStepUp48
  | ⟨8,_⟩ => exact sStepUp49
  | ⟨9,_⟩ => exact sStepUp50
  | ⟨10,_⟩ => exact sStepUp51
  | ⟨11,_⟩ => exact sStepUp52
  | ⟨12,_⟩ => exact sStepUp53
  | ⟨13,_⟩ => exact sStepUp54
  | ⟨14,_⟩ => exact sStepUp55
  | ⟨15,_⟩ => exact sStepUp56
  | ⟨16,_⟩ => exact sStepUp57
  | ⟨17,_⟩ => exact sStepUp58
  | ⟨18,_⟩ => exact sStepUp59
  | ⟨19,_⟩ => exact sStepUp60
  | ⟨20,_⟩ => exact sStepUp61
  | ⟨21,_⟩ => exact sStepUp62
  | ⟨22,_⟩ => exact sStepUp63
  | ⟨23,_⟩ => exact sStepUp64
  | ⟨24,_⟩ => exact sStepUp65
  | ⟨25,_⟩ => exact sStepUp66
  | ⟨26,_⟩ => exact sStepUp67
  | ⟨j+27,h⟩ => exact False.elim (by omega)

theorem sStepDown (j : ℕ) (hj : j < 41) : sCap (j+1) ≤ sCap j := by
  interval_cases j <;> norm_num [sCap]

theorem sStepUp (j : ℕ) (hj : 41 ≤ j) (hj' : j < 68) : sCap j ≤ sCap (j+1) := by
  have h := sStepUpFin ⟨j-41,by omega⟩
  simpa only [Fin.mk_val, Nat.sub_add_cancel hj, show j-41+42 = j+1 by omega] using h

theorem sLeft : Antitone (fun j : ℕ => sCap (min j 41)) := by
  apply antitone_nat_of_succ_le
  intro j
  by_cases h : j < 41
  · simpa only [min_eq_left (show j+1 ≤ 41 by omega), min_eq_left (by omega : j ≤ 41)]
      using sStepDown j h
  · rw [min_eq_right (by omega : 41 ≤ j+1), min_eq_right (by omega : 41 ≤ j)] <;> exact le_rfl

theorem sRight : Monotone (fun j : ℕ => sCap (min (max j 41) 68)) := by
  apply monotone_nat_of_le_succ
  intro j
  by_cases hl : j < 41
  · rw [max_eq_right (by omega : j ≤ 41), max_eq_right (by omega : j+1 ≤ 41)] <;> exact le_rfl
  · by_cases hu : j < 68
    · simpa only [max_eq_left (by omega : 41 ≤ j), max_eq_left (by omega : 41 ≤ j+1),
        min_eq_left (by omega : j ≤ 68), min_eq_left (by omega : j+1 ≤ 68)] using
        sStepUp j (by omega) hu
    · rw [min_eq_right (by omega : 68 ≤ max j 41),
        min_eq_right (by omega : 68 ≤ max (j+1) 41)] <;> exact le_rfl

theorem sRange {a b j : ℕ} (ha : a ≤ j) (hb : j ≤ b) (hb68 : b ≤ 68) :
    sCap j ≤ max (sCap a) (sCap b) := by
  by_cases hj : j ≤ 41
  · have h := sLeft ha
    dsimp only at h
    rw [min_eq_left hj, min_eq_left (ha.trans hj)] at h
    exact h.trans (le_max_left _ _)
  · have h := sRight hb
    dsimp only at h
    rw [max_eq_left (by omega : 41 ≤ j), max_eq_left (by omega : 41 ≤ b),
      min_eq_left (hb.trans hb68), min_eq_left hb68] at h
    exact h.trans (le_max_right _ _)

theorem sNode_mono : Monotone sNode := by
  intro i j h
  have : (i : ℝ) ≤ j := by exact_mod_cast h
  unfold sNode
  linarith

theorem sFromRange {n : ℕ} (hn : 11883 ≤ n) {lo hi ks c : ℝ} (a b : ℕ)
    (ha : sNode a < lo) (hb : hi < sNode (b+1)) (hb68 : b ≤ 68)
    (hk : max (sCap a) (sCap b) ≤ ks) (hc : B lo hi c) : SConditions (n := n) c ks := by
  have hstart : sNode 0 ≤ c := (sNode_mono (Nat.zero_le a)).trans (ha.le.trans hc.1)
  have hend : c ≤ sNode 69 := hc.2.trans (hb.le.trans (sNode_mono (by omega)))
  obtain ⟨j, hj, hcell⟩ := BstLean.Part193.chain_coverage sNode
    (by norm_num : 0 < 69) (fun j _ => sNode_mono (Nat.le_succ j)) ⟨hstart,hend⟩
  have hj69 : j < 69 := Finset.mem_range.mp hj
  have hja : a ≤ j := by
    have hlt : (a : ℝ) < j+1 := by
      have := hcell.2
      unfold sNode at ha this
      push_cast at this
      linarith [hc.1]
    have : a < j+1 := by exact_mod_cast hlt
    omega
  have hjb : j ≤ b := by
    have hlt : (j : ℝ) < b+1 := by
      have := hcell.1
      unfold sNode at hb this
      push_cast at hb
      linarith [hc.2]
    have : j < b+1 := by exact_mod_cast hlt
    omega
  have hs := sGrid hn ⟨j,hj69⟩ hcell
  have hcap := (sRange hja hjb hb68).trans hk
  exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    hs.2.2.2.2.2.2.trans (mul_le_mul_of_nonneg_left hcap (by positivity))⟩

theorem sClass10W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨0,by decide⟩).wlo (parameters ⟨0,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨0,by decide⟩).wS := by
  exact sFromRange hn 10 68 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass10C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨0,by decide⟩).clo (parameters ⟨0,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨0,by decide⟩).cS := by
  exact sFromRange hn 23 50 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass11W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨1,by decide⟩).wlo (parameters ⟨1,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨1,by decide⟩).wS := by
  exact sFromRange hn 10 67 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass11C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨1,by decide⟩).clo (parameters ⟨1,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨1,by decide⟩).cS := by
  exact sFromRange hn 23 50 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass12W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨2,by decide⟩).wlo (parameters ⟨2,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨2,by decide⟩).wS := by
  exact sFromRange hn 10 67 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass12C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨2,by decide⟩).clo (parameters ⟨2,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨2,by decide⟩).cS := by
  exact sFromRange hn 23 50 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass13W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨3,by decide⟩).wlo (parameters ⟨3,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨3,by decide⟩).wS := by
  exact sFromRange hn 10 67 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass13C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨3,by decide⟩).clo (parameters ⟨3,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨3,by decide⟩).cS := by
  exact sFromRange hn 23 49 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass14W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨4,by decide⟩).wlo (parameters ⟨4,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨4,by decide⟩).wS := by
  exact sFromRange hn 9 67 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass14C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨4,by decide⟩).clo (parameters ⟨4,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨4,by decide⟩).cS := by
  exact sFromRange hn 22 49 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass15W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨5,by decide⟩).wlo (parameters ⟨5,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨5,by decide⟩).wS := by
  exact sFromRange hn 9 66 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass15C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨5,by decide⟩).clo (parameters ⟨5,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨5,by decide⟩).cS := by
  exact sFromRange hn 22 49 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass16W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨6,by decide⟩).wlo (parameters ⟨6,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨6,by decide⟩).wS := by
  exact sFromRange hn 9 66 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass16C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨6,by decide⟩).clo (parameters ⟨6,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨6,by decide⟩).cS := by
  exact sFromRange hn 22 49 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass17W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨7,by decide⟩).wlo (parameters ⟨7,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨7,by decide⟩).wS := by
  exact sFromRange hn 9 66 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass17C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨7,by decide⟩).clo (parameters ⟨7,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨7,by decide⟩).cS := by
  exact sFromRange hn 22 48 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass18W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨8,by decide⟩).wlo (parameters ⟨8,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨8,by decide⟩).wS := by
  exact sFromRange hn 8 66 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass18C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨8,by decide⟩).clo (parameters ⟨8,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨8,by decide⟩).cS := by
  exact sFromRange hn 21 48 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass19W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨9,by decide⟩).wlo (parameters ⟨9,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨9,by decide⟩).wS := by
  exact sFromRange hn 8 65 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass19C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨9,by decide⟩).clo (parameters ⟨9,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨9,by decide⟩).cS := by
  exact sFromRange hn 21 48 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass20W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨10,by decide⟩).wlo (parameters ⟨10,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨10,by decide⟩).wS := by
  exact sFromRange hn 8 65 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass20C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨10,by decide⟩).clo (parameters ⟨10,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨10,by decide⟩).cS := by
  exact sFromRange hn 21 48 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass21W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨11,by decide⟩).wlo (parameters ⟨11,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨11,by decide⟩).wS := by
  exact sFromRange hn 8 65 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass21C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨11,by decide⟩).clo (parameters ⟨11,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨11,by decide⟩).cS := by
  exact sFromRange hn 21 47 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass22W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨12,by decide⟩).wlo (parameters ⟨12,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨12,by decide⟩).wS := by
  exact sFromRange hn 7 65 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass22C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨12,by decide⟩).clo (parameters ⟨12,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨12,by decide⟩).cS := by
  exact sFromRange hn 20 47 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass23W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨13,by decide⟩).wlo (parameters ⟨13,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨13,by decide⟩).wS := by
  exact sFromRange hn 7 65 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass23C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨13,by decide⟩).clo (parameters ⟨13,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨13,by decide⟩).cS := by
  exact sFromRange hn 20 47 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass24W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨14,by decide⟩).wlo (parameters ⟨14,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨14,by decide⟩).wS := by
  exact sFromRange hn 7 64 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass24C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨14,by decide⟩).clo (parameters ⟨14,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨14,by decide⟩).cS := by
  exact sFromRange hn 20 47 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass25W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨15,by decide⟩).wlo (parameters ⟨15,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨15,by decide⟩).wS := by
  exact sFromRange hn 7 64 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass25C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨15,by decide⟩).clo (parameters ⟨15,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨15,by decide⟩).cS := by
  exact sFromRange hn 20 47 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass26W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨16,by decide⟩).wlo (parameters ⟨16,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨16,by decide⟩).wS := by
  exact sFromRange hn 6 64 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass26C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨16,by decide⟩).clo (parameters ⟨16,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨16,by decide⟩).cS := by
  exact sFromRange hn 19 46 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass27W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨17,by decide⟩).wlo (parameters ⟨17,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨17,by decide⟩).wS := by
  exact sFromRange hn 6 64 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass27C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨17,by decide⟩).clo (parameters ⟨17,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨17,by decide⟩).cS := by
  exact sFromRange hn 19 46 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass28W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨18,by decide⟩).wlo (parameters ⟨18,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨18,by decide⟩).wS := by
  exact sFromRange hn 6 63 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass28C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨18,by decide⟩).clo (parameters ⟨18,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨18,by decide⟩).cS := by
  exact sFromRange hn 19 46 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass29W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨19,by decide⟩).wlo (parameters ⟨19,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨19,by decide⟩).wS := by
  exact sFromRange hn 6 63 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass29C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨19,by decide⟩).clo (parameters ⟨19,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨19,by decide⟩).cS := by
  exact sFromRange hn 19 46 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass30W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨20,by decide⟩).wlo (parameters ⟨20,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨20,by decide⟩).wS := by
  exact sFromRange hn 5 63 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass30C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨20,by decide⟩).clo (parameters ⟨20,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨20,by decide⟩).cS := by
  exact sFromRange hn 18 45 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass31W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨21,by decide⟩).wlo (parameters ⟨21,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨21,by decide⟩).wS := by
  exact sFromRange hn 5 63 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass31C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨21,by decide⟩).clo (parameters ⟨21,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨21,by decide⟩).cS := by
  exact sFromRange hn 18 45 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass32W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨22,by decide⟩).wlo (parameters ⟨22,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨22,by decide⟩).wS := by
  exact sFromRange hn 5 62 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass32C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨22,by decide⟩).clo (parameters ⟨22,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨22,by decide⟩).cS := by
  exact sFromRange hn 18 45 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass33W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨23,by decide⟩).wlo (parameters ⟨23,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨23,by decide⟩).wS := by
  exact sFromRange hn 5 62 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass33C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨23,by decide⟩).clo (parameters ⟨23,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨23,by decide⟩).cS := by
  exact sFromRange hn 18 45 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass34W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨24,by decide⟩).wlo (parameters ⟨24,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨24,by decide⟩).wS := by
  exact sFromRange hn 4 62 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass34C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨24,by decide⟩).clo (parameters ⟨24,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨24,by decide⟩).cS := by
  exact sFromRange hn 17 44 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass35W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨25,by decide⟩).wlo (parameters ⟨25,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨25,by decide⟩).wS := by
  exact sFromRange hn 4 62 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass35C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨25,by decide⟩).clo (parameters ⟨25,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨25,by decide⟩).cS := by
  exact sFromRange hn 17 44 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass36W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨26,by decide⟩).wlo (parameters ⟨26,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨26,by decide⟩).wS := by
  exact sFromRange hn 4 62 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass36C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨26,by decide⟩).clo (parameters ⟨26,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨26,by decide⟩).cS := by
  exact sFromRange hn 17 44 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass37W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨27,by decide⟩).wlo (parameters ⟨27,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨27,by decide⟩).wS := by
  exact sFromRange hn 4 61 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass37C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨27,by decide⟩).clo (parameters ⟨27,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨27,by decide⟩).cS := by
  exact sFromRange hn 17 44 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass38W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨28,by decide⟩).wlo (parameters ⟨28,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨28,by decide⟩).wS := by
  exact sFromRange hn 3 61 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass38C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨28,by decide⟩).clo (parameters ⟨28,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨28,by decide⟩).cS := by
  exact sFromRange hn 17 43 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass39W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨29,by decide⟩).wlo (parameters ⟨29,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨29,by decide⟩).wS := by
  exact sFromRange hn 3 61 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass39C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨29,by decide⟩).clo (parameters ⟨29,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨29,by decide⟩).cS := by
  exact sFromRange hn 16 43 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass40W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨30,by decide⟩).wlo (parameters ⟨30,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨30,by decide⟩).wS := by
  exact sFromRange hn 3 61 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass40C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨30,by decide⟩).clo (parameters ⟨30,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨30,by decide⟩).cS := by
  exact sFromRange hn 16 43 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass41W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨31,by decide⟩).wlo (parameters ⟨31,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨31,by decide⟩).wS := by
  exact sFromRange hn 3 60 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass41C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨31,by decide⟩).clo (parameters ⟨31,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨31,by decide⟩).cS := by
  exact sFromRange hn 16 43 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass42W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨32,by decide⟩).wlo (parameters ⟨32,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨32,by decide⟩).wS := by
  exact sFromRange hn 3 60 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass42C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨32,by decide⟩).clo (parameters ⟨32,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨32,by decide⟩).cS := by
  exact sFromRange hn 16 42 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass43W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨33,by decide⟩).wlo (parameters ⟨33,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨33,by decide⟩).wS := by
  exact sFromRange hn 2 60 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass43C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨33,by decide⟩).clo (parameters ⟨33,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨33,by decide⟩).cS := by
  exact sFromRange hn 15 42 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass44W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨34,by decide⟩).wlo (parameters ⟨34,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨34,by decide⟩).wS := by
  exact sFromRange hn 2 60 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass44C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨34,by decide⟩).clo (parameters ⟨34,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨34,by decide⟩).cS := by
  exact sFromRange hn 15 42 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass45W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨35,by decide⟩).wlo (parameters ⟨35,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨35,by decide⟩).wS := by
  exact sFromRange hn 2 59 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass45C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨35,by decide⟩).clo (parameters ⟨35,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨35,by decide⟩).cS := by
  exact sFromRange hn 15 42 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass46W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨36,by decide⟩).wlo (parameters ⟨36,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨36,by decide⟩).wS := by
  exact sFromRange hn 2 59 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass46C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨36,by decide⟩).clo (parameters ⟨36,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨36,by decide⟩).cS := by
  exact sFromRange hn 15 42 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass47W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨37,by decide⟩).wlo (parameters ⟨37,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨37,by decide⟩).wS := by
  exact sFromRange hn 1 59 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass47C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨37,by decide⟩).clo (parameters ⟨37,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨37,by decide⟩).cS := by
  exact sFromRange hn 14 41 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass48W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨38,by decide⟩).wlo (parameters ⟨38,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨38,by decide⟩).wS := by
  exact sFromRange hn 1 59 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass48C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨38,by decide⟩).clo (parameters ⟨38,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨38,by decide⟩).cS := by
  exact sFromRange hn 14 41 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass49W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨39,by decide⟩).wlo (parameters ⟨39,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨39,by decide⟩).wS := by
  exact sFromRange hn 1 59 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass49C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨39,by decide⟩).clo (parameters ⟨39,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨39,by decide⟩).cS := by
  exact sFromRange hn 14 41 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass50W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨40,by decide⟩).wlo (parameters ⟨40,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨40,by decide⟩).wS := by
  exact sFromRange hn 1 58 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass50C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨40,by decide⟩).clo (parameters ⟨40,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨40,by decide⟩).cS := by
  exact sFromRange hn 14 41 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass51W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨41,by decide⟩).wlo (parameters ⟨41,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨41,by decide⟩).wS := by
  exact sFromRange hn 0 58 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass51C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨41,by decide⟩).clo (parameters ⟨41,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨41,by decide⟩).cS := by
  exact sFromRange hn 13 40 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass52W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨42,by decide⟩).wlo (parameters ⟨42,by decide⟩).whi c) :
    SConditions (n := n) c (parameters ⟨42,by decide⟩).wS := by
  exact sFromRange hn 0 58 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

theorem sClass52C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (parameters ⟨42,by decide⟩).clo (parameters ⟨42,by decide⟩).chi c) :
    SConditions (n := n) c (parameters ⟨42,by decide⟩).cS := by
  exact sFromRange hn 13 40 (by norm_num [sNode,parameters]) (by norm_num [sNode,parameters])
    (by norm_num) (by norm_num [sCap,parameters]) hc

end BstLean.Part281.TI
