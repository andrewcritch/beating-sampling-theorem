import BstLean.Part293Envelope11
import BstLean.Part293EndpointInterface
import BstLean.Part293MixtureNumerics
import BstLean.Part252MomentNum

namespace BstLean.Part293.Envelope
open Real

theorem rotation2_le : BstLean.Part195.rotationConstant 2 ≤ (103364223 / 50000000 : ℝ) := by
  apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem rotation4_le : BstLean.Part195.rotationConstant 4 ≤ (70260073 / 25000000 : ℝ) := by
  apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem rotation6_le : BstLean.Part195.rotationConstant 6 ≤ (169756067 / 50000000 : ℝ) := by
  apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem rotation8_le : BstLean.Part195.rotationConstant 8 ≤ (389312743 / 100000000 : ℝ) := by
  apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem rotation12_le : BstLean.Part195.rotationConstant 12 ≤ (236731997 / 50000000 : ℝ) := by
  apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

noncomputable def H (x : ℝ) : ℝ := v7 x

theorem H_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ H x ∧ H x ≤ (2626060875000001 / 1000000000000000000 : ℝ) :=
  v7_bounds x hx0 hx1

noncomputable def mu (x : ℝ) : ℝ := v11 x

theorem mu_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (105161185805410163 / 125000000000000000 : ℝ) ≤ mu x ∧ mu x ≤ (105485506007910741 / 125000000000000000 : ℝ) :=
  v11_bounds x hx0 hx1

noncomputable def Y0 (x : ℝ) : ℝ := v13 x

theorem Y0_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (287859713424321723 / 1000000000000000000 : ℝ) ≤ Y0 x ∧ Y0 x ≤ (146116000000000003 / 500000000000000000 : ℝ) :=
  v13_bounds x hx0 hx1

noncomputable def V (x : ℝ) : ℝ := v18 x

theorem V_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ V x ∧ V x ≤ (47549080909 / 1000000000000000000 : ℝ) :=
  v18_bounds x hx0 hx1

noncomputable def dw (x : ℝ) : ℝ := v26 x

theorem dw_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ dw x ∧ dw x ≤ (3618464091713129 / 1000000000000000000 : ℝ) :=
  v26_bounds x hx0 hx1

noncomputable def chi (x : ℝ) : ℝ := v32 x

theorem chi_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499999999999999999 / 500000000000000000 : ℝ) ≤ chi x ∧ chi x ≤ (67528729182759273 / 62500000000000000 : ℝ) :=
  v32_bounds x hx0 hx1

noncomputable def gap (x : ℝ) : ℝ := v38 x

theorem gap_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (10872132493885707 / 200000000000000000 : ℝ) ≤ gap x ∧ gap x ≤ (28477612044716581 / 500000000000000000 : ℝ) :=
  v38_bounds x hx0 hx1

noncomputable def B (x : ℝ) : ℝ := v47 x

theorem B_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (175143 / 1000000000000000000 : ℝ) ≤ B x ∧ B x ≤ (233201 / 125000000000000000 : ℝ) :=
  v47_bounds x hx0 hx1

noncomputable def removal (x : ℝ) : ℝ := v49 x

theorem removal_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (8842602444981 / 1000000000000000000 : ℝ) ≤ removal x ∧ removal x ≤ (14429919689659 / 500000000000000000 : ℝ) :=
  v49_bounds x hx0 hx1

noncomputable def G (x : ℝ) : ℝ := v140 x

theorem G_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3421938733608913391 / 1000000000000000000 : ℝ) ≤ G x ∧ G x ≤ (930533566165383529 / 250000000000000000 : ℝ) :=
  v140_bounds x hx0 hx1

noncomputable def Gamma (x : ℝ) : ℝ := v189 x

theorem Gamma_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3421938733608913391 / 1000000000000000000 : ℝ) ≤ Gamma x ∧ Gamma x ≤ (93021621740320847 / 25000000000000000 : ℝ) :=
  v189_bounds x hx0 hx1

noncomputable def eps (x : ℝ) : ℝ := v195 x

theorem eps_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (-1 / 250000000000000000 : ℝ) ≤ eps x ∧ eps x ≤ (34406168453805397 / 1000000000000000000 : ℝ) :=
  v195_bounds x hx0 hx1

noncomputable def kap (x : ℝ) : ℝ := v198 x

theorem kap_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (249999999999999999 / 250000000000000000 : ℝ) ≤ kap x ∧ kap x ≤ (1001185187434099997 / 1000000000000000000 : ℝ) :=
  v198_bounds x hx0 hx1

noncomputable def L (x : ℝ) : ℝ := v208 x

theorem L_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ L x ∧ L x ≤ (502996036355506941 / 200000000000000000 : ℝ) :=
  v208_bounds x hx0 hx1

noncomputable def factor (x : ℝ) : ℝ := v215 x

theorem factor_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (6874814130806455803 / 500000000000000000 : ℝ) ≤ factor x ∧ factor x ≤ (1901504622888185021 / 125000000000000000 : ℝ) :=
  v215_bounds x hx0 hx1

noncomputable def A (x : ℝ) : ℝ := v216 x

theorem A_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ A x ∧ A x ≤ (361659188651 / 500000000000000000 : ℝ) :=
  v216_bounds x hx0 hx1

noncomputable def An (x : ℝ) : ℝ := v221 x

theorem An_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ An x ∧ An x ≤ (1446636754489399 / 250000000000000000 : ℝ) :=
  v221_bounds x hx0 hx1

noncomputable def D (x : ℝ) : ℝ := v228 x

theorem D_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ D x ∧ D x ≤ (1536708324051821 / 1000000000000000000 : ℝ) :=
  v228_bounds x hx0 hx1

noncomputable def n_eps2 (x : ℝ) : ℝ := v241 x

theorem n_eps2_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ n_eps2 x ∧ n_eps2 x ≤ (1183784427671626091 / 125000000000000000 : ℝ) :=
  v241_bounds x hx0 hx1

noncomputable def cap (x : ℝ) : ℝ := v246 x

theorem cap_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ cap x ∧ cap x ≤ (7345344028132653347 / 1000000000000000000 : ℝ) :=
  v246_bounds x hx0 hx1

noncomputable def T2 (x : ℝ) : ℝ := v253 x

theorem T2_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ T2 x ∧ T2 x ≤ (4488167100832457 / 1000000000000000000 : ℝ) :=
  v253_bounds x hx0 hx1

noncomputable def T4 (x : ℝ) : ℝ := v287 x

theorem T4_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ T4 x ∧ T4 x ≤ (305425113412679 / 5000000000000000 : ℝ) :=
  v287_bounds x hx0 hx1

noncomputable def T6 (x : ℝ) : ℝ := v321 x

theorem T6_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ T6 x ∧ T6 x ≤ (5572549237563979 / 62500000000000000 : ℝ) :=
  v321_bounds x hx0 hx1

noncomputable def chi2 (x : ℝ) : ℝ := v346 x

theorem chi2_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ chi2 x ∧ chi2 x ≤ (14573105493703 / 1000000000000000000 : ℝ) :=
  v346_bounds x hx0 hx1

noncomputable def ell (x : ℝ) : ℝ := v363 x

theorem ell_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ ell x ∧ ell x ≤ (2429203534280479 / 1000000000000000000 : ℝ) :=
  v363_bounds x hx0 hx1

noncomputable def mix (x : ℝ) : ℝ := v368 x

theorem mix_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ mix x ∧ mix x ≤ (386227144994911 / 200000000000000000 : ℝ) :=
  v368_bounds x hx0 hx1

noncomputable def Dd (x : ℝ) : ℝ := v383 x

theorem Dd_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ Dd x ∧ Dd x ≤ (32262610339 / 250000000000000000 : ℝ) :=
  v383_bounds x hx0 hx1

noncomputable def displacement (x : ℝ) : ℝ := v384 x

theorem displacement_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ displacement x ∧ displacement x ≤ (359235913232517 / 1000000000000000000 : ℝ) :=
  v384_bounds x hx0 hx1

noncomputable def af (x : ℝ) : ℝ := v454 x

theorem af_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (23632882299999999 / 500000000000000000 : ℝ) ≤ af x ∧ af x ≤ (5123185055347893 / 100000000000000000 : ℝ) :=
  v454_bounds x hx0 hx1

noncomputable def aw (x : ℝ) : ℝ := v456 x

theorem aw_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (86309815199999999 / 500000000000000000 : ℝ) ≤ aw x ∧ aw x ≤ (180159935240663019 / 1000000000000000000 : ℝ) :=
  v456_bounds x hx0 hx1

noncomputable def F8 (x : ℝ) : ℝ := v460 x

theorem F8_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (841289486443281303 / 1000000000000000000 : ℝ) ≤ F8 x ∧ F8 x ≤ (854271709379027663 / 1000000000000000000 : ℝ) :=
  v460_bounds x hx0 hx1

noncomputable def F24 (x : ℝ) : ℝ := v464 x

theorem F24_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (841289486443281303 / 1000000000000000000 : ℝ) ≤ F24 x ∧ F24 x ≤ (172276794315825923 / 200000000000000000 : ℝ) :=
  v464_bounds x hx0 hx1

noncomputable def Cv (x : ℝ) : ℝ := v468 x

theorem Cv_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ Cv x ∧ Cv x ≤ (380392647242719 / 1000000000000000000 : ℝ) :=
  v468_bounds x hx0 hx1

noncomputable def vmax (x : ℝ) : ℝ := v491 x

theorem vmax_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ vmax x ∧ vmax x ≤ (4100109663595267 / 1000000000000000000 : ℝ) :=
  v491_bounds x hx0 hx1

noncomputable def threshold (x : ℝ) : ℝ := v493 x

theorem threshold_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2559323445517977 / 500000000000000000 : ℝ) ≤ threshold x ∧ threshold x ≤ (28000000000000001 / 1000000000000000000 : ℝ) :=
  v493_bounds x hx0 hx1

noncomputable def bias (x : ℝ) : ℝ := v510 x

theorem bias_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ bias x ∧ bias x ≤ (4044231734383677 / 1000000000000000000 : ℝ) :=
  v510_bounds x hx0 hx1

noncomputable def total (x : ℝ) : ℝ := v515 x

theorem total_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (553912652811 / 62500000000000000 : ℝ) ≤ total x ∧ total x ≤ (6363483211970073 / 1000000000000000000 : ℝ) :=
  v515_bounds x hx0 hx1

noncomputable def iota4 (x : ℝ) : ℝ := v260 x

theorem iota4_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1067949201436327603 / 1000000000000000000 : ℝ) ≤ iota4 x ∧ iota4 x ≤ (67281078619077483 / 62500000000000000 : ℝ) :=
  v260_bounds x hx0 hx1

noncomputable def ecoef4 (x : ℝ) : ℝ := v267 x

theorem ecoef4_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1258590203830642443 / 250000000000000000 : ℝ) ≤ ecoef4 x ∧ ecoef4 x ≤ (5117937480762989099 / 1000000000000000000 : ℝ) :=
  v267_bounds x hx0 hx1

noncomputable def dcoef4 (x : ℝ) : ℝ := v270 x

theorem dcoef4_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1258590203830642443 / 500000000000000000 : ℝ) ≤ dcoef4 x ∧ dcoef4 x ≤ (527486016100111983 / 200000000000000000 : ℝ) :=
  v270_bounds x hx0 hx1

noncomputable def ntau4 (x : ℝ) : ℝ := v276 x

theorem ntau4_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ ntau4 x ∧ ntau4 x ≤ (46980245413373 / 15625000000000000 : ℝ) :=
  v276_bounds x hx0 hx1

noncomputable def iota6 (x : ℝ) : ℝ := v294 x

theorem iota6_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (213552237996525131 / 200000000000000000 : ℝ) ≤ iota6 x ∧ iota6 x ≤ (53815462322576889 / 50000000000000000 : ℝ) :=
  v294_bounds x hx0 hx1

noncomputable def ecoef6 (x : ℝ) : ℝ := v301 x

theorem ecoef6_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1258368630207553463 / 250000000000000000 : ℝ) ≤ ecoef6 x ∧ ecoef6 x ≤ (204681745089627971 / 40000000000000000 : ℝ) :=
  v301_bounds x hx0 hx1

noncomputable def dcoef6 (x : ℝ) : ℝ := v304 x

theorem dcoef6_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1258368630207553463 / 500000000000000000 : ℝ) ≤ dcoef6 x ∧ dcoef6 x ≤ (2636969450378345701 / 1000000000000000000 : ℝ) :=
  v304_bounds x hx0 hx1

noncomputable def ntau6 (x : ℝ) : ℝ := v310 x

theorem ntau6_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ ntau6 x ∧ ntau6 x ≤ (2195109202099023 / 500000000000000000 : ℝ) :=
  v310_bounds x hx0 hx1

noncomputable def tau12 (x : ℝ) : ℝ := v123 x

theorem tau12_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ tau12 x ∧ tau12 x ≤ (64615430209163 / 62500000000000000 : ℝ) :=
  v123_bounds x hx0 hx1

noncomputable def tau4 (x : ℝ) : ℝ := v71 x

theorem tau4_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ tau4 x ∧ tau4 x ≤ (122611902082463 / 200000000000000000 : ℝ) :=
  v71_bounds x hx0 hx1

noncomputable def tau8 (x : ℝ) : ℝ := v97 x

theorem tau8_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ tau8 x ∧ tau8 x ≤ (424834884073099 / 500000000000000000 : ℝ) :=
  v97_bounds x hx0 hx1

noncomputable def X4 (x : ℝ) : ℝ := v152 x

theorem X4_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ X4 x ∧ X4 x ≤ (73024954083059 / 4000000000000000 : ℝ) :=
  v152_bounds x hx0 hx1

noncomputable def X8 (x : ℝ) : ℝ := v164 x

theorem X8_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ X8 x ∧ X8 x ≤ (5747786208335649 / 250000000000000000 : ℝ) :=
  v164_bounds x hx0 hx1

noncomputable def X12 (x : ℝ) : ℝ := v176 x

theorem X12_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ X12 x ∧ X12 x ≤ (668448633123863 / 25000000000000000 : ℝ) :=
  v176_bounds x hx0 hx1

noncomputable def Xhat4 (x : ℝ) : ℝ := v75 x

theorem Xhat4_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ Xhat4 x ∧ Xhat4 x ≤ (18338939022491519 / 1000000000000000000 : ℝ) :=
  v75_bounds x hx0 hx1

noncomputable def Xhat8 (x : ℝ) : ℝ := v101 x

theorem Xhat8_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ Xhat8 x ∧ Xhat8 x ≤ (11552872575528357 / 500000000000000000 : ℝ) :=
  v101_bounds x hx0 hx1

noncomputable def Xhat12 (x : ℝ) : ℝ := v127 x

theorem Xhat12_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ Xhat12 x ∧ Xhat12 x ≤ (13438688208858603 / 500000000000000000 : ℝ) :=
  v127_bounds x hx0 hx1

theorem H_formula (x : ℝ) :
    H x = (x * (21008487 / 1000000 : ℝ)) := rfl

theorem mu_formula (x : ℝ) :
    mu x = ((√(88471 / 125000 : ℝ)) + (√(x * (26927 / 500000 : ℝ)))) := rfl

theorem Y0_formula (x : ℝ) :
    Y0 x = ((1 : ℝ) - ((mu x) ^ 2)) := rfl

theorem V_formula (x : ℝ) :
    V x = (((x * (1521 / 500 : ℝ)) * x) / ((1 : ℝ) - (x * (3 : ℝ)))) := rfl

theorem dw_formula (x : ℝ) :
    dw x = (((((BstLean.Part195.rotationConstant 12) * (√(1521 / 500 : ℝ))) * x) / (√((1 : ℝ) - (x * (25 : ℝ))))) * (7 / 2 : ℝ)) := rfl

theorem chi_formula (x : ℝ) :
    chi x = ((((√(x * (12 : ℝ))) * (2 : ℝ)) + (1 : ℝ)) + (x * (24 : ℝ))) := rfl

theorem gap_formula (x : ℝ) :
    gap x = (((√(20171089 / 25000000 : ℝ)) - (√(88471 / 125000 : ℝ))) - (√(x * (26927 / 500000 : ℝ)))) := rfl

theorem B_formula (x : ℝ) :
    B x = (((((H x) / (33 / 5000 : ℝ)) ^ 32) + ((((BstLean.Part195.rotationConstant 12) * (√(x * (27323 / 250000 : ℝ)))) / (gap x)) ^ 24)) + (33554432 / 191581231380566414401 : ℝ)) := rfl

theorem removal_formula (x : ℝ) :
    removal x = (√((B x) * (4018 / 9 : ℝ))) := rfl

theorem G_formula (x : ℝ) :
    G x = (((((1 : ℝ) / (Y0 x)) + ((Xhat4 x) / ((Y0 x) ^ 2))) + (((Xhat8 x) ^ 2) / ((Y0 x) ^ 3))) + (((Xhat12 x) ^ 3) / (((Y0 x) ^ 3) * (9 / 50 : ℝ)))) := rfl

theorem Gamma_formula (x : ℝ) :
    Gamma x = (((((1 : ℝ) / (Y0 x)) + ((X4 x) / ((Y0 x) ^ 2))) + (((X8 x) ^ 2) / ((Y0 x) ^ 3))) + (((X12 x) ^ 3) / (((Y0 x) ^ 3) * (17919 / 100000 : ℝ)))) := rfl

theorem eps_formula (x : ℝ) :
    eps x = ((((((dw x) * (2 : ℝ)) / (√(9 / 50 : ℝ))) + (1 : ℝ)) ^ 2) - (1 : ℝ)) := rfl

theorem kap_formula (x : ℝ) :
    kap x = ((1 : ℝ) / ((1 : ℝ) - ((eps x) ^ 2))) := rfl

theorem L_formula (x : ℝ) :
    L x = ((((((((chi x) / (9 / 50 : ℝ)) * (4 : ℝ)) * (49 / 4 : ℝ)) * ((BstLean.Part195.rotationConstant 12) ^ 2)) * (1521 / 500 : ℝ)) * x) / ((1 : ℝ) - (x * (25 : ℝ)))) := rfl

theorem factor_formula (x : ℝ) :
    factor x = (((((((dw x) / (√(9 / 50 : ℝ))) + (1 : ℝ)) ^ 2) * (4 : ℝ)) / (1991 / 2000 : ℝ)) * (G x)) := rfl

theorem A_formula (x : ℝ) :
    A x = ((factor x) * (V x)) := rfl

theorem An_formula (x : ℝ) :
    An x = ((((factor x) * (1521 / 500 : ℝ)) * x) / ((1 : ℝ) - (x * (3 : ℝ)))) := rfl

theorem D_formula (x : ℝ) :
    D x = ((((((chi x) / (1991 / 2000 : ℝ)) * (G x)) * (1521 / 500 : ℝ)) * x) / ((1 : ℝ) - (x * (3 : ℝ)))) := rfl

theorem n_eps2_formula (x : ℝ) :
    n_eps2 x = (((((((BstLean.Part195.rotationConstant 12) ^ 2) * (196 : ℝ)) * (1521 / 500 : ℝ)) * x) / (((1 : ℝ) - (x * (25 : ℝ))) * (9 / 50 : ℝ))) * ((((dw x) / (√(9 / 50 : ℝ))) + (1 : ℝ)) ^ 2)) := rfl

theorem cap_formula (x : ℝ) :
    cap x = ((kap x) * (((n_eps2 x) / (2 : ℝ)) + ((L x) * ((eps x) + (1 : ℝ))))) := rfl

theorem T2_formula (x : ℝ) :
    T2 x = ((kap x) * ((((An x) / (2 : ℝ)) + (D x)) + (√(((L x) * (A x)) * (D x))))) := rfl

theorem T4_formula (x : ℝ) :
    T4 x = (((kap x) * (ntau4 x)) * (((((ecoef4 x) ^ 2) / (2 : ℝ)) + ((dcoef4 x) ^ 2)) + (((√((L x) * x)) * (ecoef4 x)) * (dcoef4 x)))) := rfl

theorem T6_formula (x : ℝ) :
    T6 x = (((kap x) * (ntau6 x)) * (((((ecoef6 x) ^ 2) / (2 : ℝ)) + ((dcoef6 x) ^ 2)) + (((√((L x) * x)) * (ecoef6 x)) * (dcoef6 x)))) := rfl

theorem chi2_formula (x : ℝ) :
    chi2 x = (((((((kap x) * ((((An x) * (A x)) / (4 : ℝ)) + ((((eps x) + (1 : ℝ)) * (A x)) * (D x)))) + (((T2 x) ^ 2) / (2 : ℝ))) + (((T2 x) * ((T4 x) ^ 2)) / (6 : ℝ))) + (((T4 x) ^ 4) / (24 : ℝ))) + (((T6 x) ^ 5) / (120 : ℝ))) + (((exp (cap x)) * ((T6 x) ^ 6)) / (720 : ℝ))) := rfl

theorem ell_formula (x : ℝ) :
    ell x = ((((An x) / ((((1 : ℝ) - (eps x)) ^ 2) * (4 : ℝ))) + ((D x) / (((1 : ℝ) - (eps x)) * (2 : ℝ)))) + (((√((A x) * (D x))) + ((√(x / (2 : ℝ))) * (An x))) / ((1 : ℝ) - (eps x)))) := rfl

theorem mix_formula (x : ℝ) :
    mix x = (√(((chi2 x) / (4 : ℝ)) + (((ell x) ^ 3) * (6 : ℝ)))) := rfl

theorem Dd_formula (x : ℝ) :
    Dd x = (((√(B x)) / (1991 / 2000 : ℝ)) * (((D x) / (2 : ℝ)) + (((((((H x) + (1 : ℝ)) ^ 2) * ((BstLean.Part195.rotationConstant 4) ^ 2)) * (1521 / 500 : ℝ)) * x) / (((1 : ℝ) - (x * (9 : ℝ))) * (81 / 2500 : ℝ))))) := rfl

theorem displacement_formula (x : ℝ) :
    displacement x = (√(Dd x)) := rfl

theorem af_formula (x : ℝ) :
    af x = ((((((19 / 100 : ℝ) * (((√(x / ((1 : ℝ) - x))) * (2 : ℝ)) * (((√x) + (1 : ℝ)) + (x * (6 : ℝ))))) * (√((1 : ℝ) - (((√(23 / 50 : ℝ)) - ((√(x * (27 / 50 : ℝ))) * (6 : ℝ))) ^ 2)))) / ((1 : ℝ) - (x * (√x)))) + (236328823 / 5000000000 : ℝ)) + ((((√(x * (27 / 50 : ℝ))) * (24 : ℝ)) * ((((√x) + (1 : ℝ)) + (x * (6 : ℝ))) * ((x * (3 : ℝ)) + (1 : ℝ)))) / ((√((1 : ℝ) - (((√(27 / 50 : ℝ)) + ((√(x * (23 / 50 : ℝ))) * (6 : ℝ))) ^ 2))) * (512 : ℝ)))) := rfl

theorem aw_formula (x : ℝ) :
    aw x = ((((((((9 / 100 : ℝ) * (4 : ℝ)) * ((1 : ℝ) - (((√(23 / 50 : ℝ)) - ((√(x * (27 / 50 : ℝ))) * (6 : ℝ))) ^ 2))) * (√x)) * ((((√x) + (1 : ℝ)) + (x * (6 : ℝ))) ^ 2)) / (((1 : ℝ) - x) * ((1 : ℝ) - (x * (√x))))) + (107887269 / 625000000 : ℝ)) + ((((√(x * (27 / 50 : ℝ))) * (192 : ℝ)) * (((((√x) + (1 : ℝ)) + (x * (6 : ℝ))) * ((x * (3 : ℝ)) + (1 : ℝ))) ^ 2)) / ((√((1 : ℝ) - (((√(27 / 50 : ℝ)) + ((√(x * (23 / 50 : ℝ))) * (6 : ℝ))) ^ 2))) * (512 : ℝ)))) := rfl

theorem F8_formula (x : ℝ) :
    F8 x = ((mu x) + ((BstLean.Part195.rotationConstant 4) * (√(x * (27323 / 250000 : ℝ))))) := rfl

theorem F24_formula (x : ℝ) :
    F24 x = ((mu x) + ((BstLean.Part195.rotationConstant 12) * (√(x * (27323 / 250000 : ℝ))))) := rfl

theorem Cv_formula (x : ℝ) :
    Cv x = ((x * (1521 / 500 : ℝ)) / ((1 : ℝ) - (x * (3 : ℝ)))) := rfl

theorem vmax_formula (x : ℝ) :
    vmax x = ((((((((√x) + (1 : ℝ)) + (x * (6 : ℝ))) * ((x * (3 : ℝ)) + (1 : ℝ))) ^ 2) * (32 : ℝ)) * x) / ((1 : ℝ) - (x * (2 : ℝ)))) := rfl

theorem threshold_formula (x : ℝ) :
    threshold x = ((7 / 250 : ℝ) - ((vmax x) / (17919 / 100000 : ℝ))) := rfl

theorem bias_formula (x : ℝ) :
    bias x = (√(((((((chi x) * (Gamma x)) / (493 / 125 : ℝ)) * ((af x) ^ 2)) + (((((((aw x) + (((F8 x) * (2 : ℝ)) * (af x))) + (((af x) ^ 2) * x)) * (Gamma x)) + ((Cv x) / (17919 / 100000 : ℝ))) ^ 2) / (972 / 125 : ℝ))) * x) + (((((((aw x) + (((F24 x) * (2 : ℝ)) * (af x))) * x) / ((threshold x) * (1773981 / 10000000 : ℝ))) ^ 6) + ((((((af x) ^ 2) * x) * x) / ((threshold x) * (17919 / 10000000 : ℝ))) ^ 4)) * (2 : ℝ)))) := rfl

theorem total_formula (x : ℝ) :
    total x = ((((((removal x) + (mix x)) + (displacement x)) + (bias x)) + (1 / 50000000 : ℝ)) + (1 / 100000000000000000000 : ℝ)) := rfl

theorem iota4_formula (x : ℝ) :
    iota4 x = ((((2000 / 1991 : ℝ) ^ ((8 : ℝ)⁻¹)) + ((√(9 / 2000 : ℝ)) / (1991 / 2000 : ℝ))) + ((dw x) / (√(17919 / 100000 : ℝ)))) := rfl

theorem ecoef4_formula (x : ℝ) :
    ecoef4 x = ((((((dw x) * (2 : ℝ)) / (√(9 / 50 : ℝ))) + (2 : ℝ)) / (√(9 / 50 : ℝ))) * (iota4 x)) := rfl

theorem dcoef4_formula (x : ℝ) :
    dcoef4 x = ((√((chi x) / (9 / 50 : ℝ))) * (iota4 x)) := rfl

theorem ntau4_formula (x : ℝ) :
    ntau4 x = (((((BstLean.Part195.rotationConstant 4) ^ 2) * (1521 / 500 : ℝ)) * x) / ((1 : ℝ) - (x * (9 : ℝ)))) := rfl

theorem iota6_formula (x : ℝ) :
    iota6 x = ((((2000 / 1991 : ℝ) ^ ((12 : ℝ)⁻¹)) + ((√(9 / 2000 : ℝ)) / (1991 / 2000 : ℝ))) + ((dw x) / (√(17919 / 100000 : ℝ)))) := rfl

theorem ecoef6_formula (x : ℝ) :
    ecoef6 x = ((((((dw x) * (2 : ℝ)) / (√(9 / 50 : ℝ))) + (2 : ℝ)) / (√(9 / 50 : ℝ))) * (iota6 x)) := rfl

theorem dcoef6_formula (x : ℝ) :
    dcoef6 x = ((√((chi x) / (9 / 50 : ℝ))) * (iota6 x)) := rfl

theorem ntau6_formula (x : ℝ) :
    ntau6 x = (((((BstLean.Part195.rotationConstant 6) ^ 2) * (1521 / 500 : ℝ)) * x) / ((1 : ℝ) - (x * (13 : ℝ)))) := rfl

theorem tau12_formula (x : ℝ) :
    tau12 x = ((((BstLean.Part195.rotationConstant 12) * (√(1521 / 500 : ℝ))) * x) / (√((1 : ℝ) - (x * (25 : ℝ))))) := rfl

theorem tau4_formula (x : ℝ) :
    tau4 x = ((((BstLean.Part195.rotationConstant 4) * (√(1521 / 500 : ℝ))) * x) / (√((1 : ℝ) - (x * (9 : ℝ))))) := rfl

theorem tau8_formula (x : ℝ) :
    tau8 x = ((((BstLean.Part195.rotationConstant 8) * (√(1521 / 500 : ℝ))) * x) / (√((1 : ℝ) - (x * (17 : ℝ))))) := rfl

theorem X4_formula (x : ℝ) :
    X4 x = (((((H x) * (2 : ℝ)) + ((((mu x) * (2 : ℝ)) * (BstLean.Part195.rotationConstant 2)) * (√(x * (27323 / 250000 : ℝ))))) + ((((BstLean.Part195.rotationConstant 4) ^ 2) * (27323 / 250000 : ℝ)) * x)) + (0 : ℝ)) := rfl

theorem X8_formula (x : ℝ) :
    X8 x = (((((H x) * (2 : ℝ)) + ((((mu x) * (2 : ℝ)) * (BstLean.Part195.rotationConstant 4)) * (√(x * (27323 / 250000 : ℝ))))) + ((((BstLean.Part195.rotationConstant 8) ^ 2) * (27323 / 250000 : ℝ)) * x)) + (0 : ℝ)) := rfl

theorem X12_formula (x : ℝ) :
    X12 x = (((((H x) * (2 : ℝ)) + ((((mu x) * (2 : ℝ)) * (BstLean.Part195.rotationConstant 6)) * (√(x * (27323 / 250000 : ℝ))))) + ((((BstLean.Part195.rotationConstant 12) ^ 2) * (27323 / 250000 : ℝ)) * x)) + (0 : ℝ)) := rfl

theorem Xhat4_formula (x : ℝ) :
    Xhat4 x = (((((H x) * (2 : ℝ)) + ((((mu x) * (2 : ℝ)) * (BstLean.Part195.rotationConstant 2)) * (√(x * (27323 / 250000 : ℝ))))) + ((((BstLean.Part195.rotationConstant 4) ^ 2) * (27323 / 250000 : ℝ)) * x)) + (((((√(9 / 1991 : ℝ)) * (2 : ℝ)) * ((H x) + (1 : ℝ))) * (tau4 x)) + ((V x) / (1991 / 2000 : ℝ)))) := rfl

theorem Xhat8_formula (x : ℝ) :
    Xhat8 x = (((((H x) * (2 : ℝ)) + ((((mu x) * (2 : ℝ)) * (BstLean.Part195.rotationConstant 4)) * (√(x * (27323 / 250000 : ℝ))))) + ((((BstLean.Part195.rotationConstant 8) ^ 2) * (27323 / 250000 : ℝ)) * x)) + (((((√(9 / 1991 : ℝ)) * (2 : ℝ)) * ((H x) + (1 : ℝ))) * (tau8 x)) + ((V x) / (1991 / 2000 : ℝ)))) := rfl

theorem Xhat12_formula (x : ℝ) :
    Xhat12 x = (((((H x) * (2 : ℝ)) + ((((mu x) * (2 : ℝ)) * (BstLean.Part195.rotationConstant 6)) * (√(x * (27323 / 250000 : ℝ))))) + ((((BstLean.Part195.rotationConstant 12) ^ 2) * (27323 / 250000 : ℝ)) * x)) + (((((√(9 / 1991 : ℝ)) * (2 : ℝ)) * ((H x) + (1 : ℝ))) * (tau12 x)) + ((V x) / (1991 / 2000 : ℝ)))) := rfl

theorem rootNumericsBand {n : ℕ} (hn : 8000 ≤ n) :
    total (1 / (n : ℝ)) ≤ rootAllowance := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 / 8000 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  exact (total_bounds _ hx0 hx1).2.trans (by norm_num [rootAllowance])

theorem scaled_energy_identity (x : ℝ) : A x = An x * x := by
  rw [A_formula, An_formula, V_formula]
  ring

theorem eps_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) : 0 ≤ eps x := by
  have hdw : 0 ≤ dw x := (dw_bounds x hx0 hx1).1
  have h : 0 ≤ dw x * 2 / √(9 / 50 : ℝ) := by positivity
  rw [eps_formula]
  nlinarith

theorem biasNumericsBand (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    BiasNumerics (chi x) (vmax x) (aw x) (af x) (F8 x) (F24 x) (Gamma x) (Cv x) := by
  constructor
  · have h := chi_bounds x hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := vmax_bounds x hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := aw_bounds x hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := af_bounds x hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := F8_bounds x hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := F24_bounds x hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := Gamma_bounds x hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := Cv_bounds x hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]

theorem mixtureNumericsBand {n : ℕ} (hn : 8000 ≤ n) :
    MixtureNumerics n (eps (1 / n)) (A (1 / n)) (D (1 / n))
      (chi2 (1 / n)) (B (1 / n)) (Dd (1 / n)) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hx0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hx1 : 1 / (n : ℝ) ≤ 1 / 8000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have heq : (n : ℝ) * A (1 / n) = An (1 / n) := by
    rw [scaled_energy_identity]
    field_simp
  constructor
  · have h := eps_bounds (1 / (n : ℝ)) hx0 hx1
    exact ⟨eps_nonneg _ hx0 hx1, h.2.trans (by norm_num)⟩
  · have h := A_bounds (1 / (n : ℝ)) hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := An_bounds (1 / (n : ℝ)) hx0 hx1
    rw [heq]
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := D_bounds (1 / (n : ℝ)) hx0 hx1
    constructor <;> norm_num at * <;> linarith [h.1, h.2]
  · have h := chi2_bounds (1 / (n : ℝ)) hx0 hx1
    norm_num at *; linarith [h.2]
  · have h := B_bounds (1 / (n : ℝ)) hx0 hx1
    norm_num at *; linarith [h.2]
  · have h := Dd_bounds (1 / (n : ℝ)) hx0 hx1
    norm_num at *; linarith [h.2]

end BstLean.Part293.Envelope

/-- info: 'BstLean.Part293.Envelope.rootNumericsBand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.Envelope.rootNumericsBand
