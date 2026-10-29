import BstLean.Part186CovC

/-!
# Part 186 (file `GeoP`): the core window geometry of the seven θ-pieces at `n ≥ 16 384`

No proof is left open; no `native_decide` or `axiom` is used. Windows (core pairs `Γ(3.75, 7, 3.75)`):
`[0.463, 0.614]`, `[0.453, 0.604]`, `[0.443, 0.594]`, `[0.433, 0.584]`, `[0.423, 0.575]`,
`[0.413, 0.565]`, `[0.405, 0.554]` for the pieces `[0.46, 0.47]`, …, `[0.52, 0.528]`.
-/

namespace BstLean.Part186

variable {n : ℕ}

theorem geoP_0 (hn : 16384 ≤ n) : GeoP n (46/100 : ℝ) (47/100) (463/1000) (614/1000) :=
  geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP_1 (hn : 16384 ≤ n) : GeoP n (47/100 : ℝ) (48/100) (453/1000) (604/1000) :=
  geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP_2 (hn : 16384 ≤ n) : GeoP n (48/100 : ℝ) (49/100) (443/1000) (594/1000) :=
  geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP_3 (hn : 16384 ≤ n) : GeoP n (49/100 : ℝ) (50/100) (433/1000) (584/1000) :=
  geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP_4 (hn : 16384 ≤ n) : GeoP n (50/100 : ℝ) (51/100) (423/1000) (575/1000) :=
  geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP_5 (hn : 16384 ≤ n) : GeoP n (51/100 : ℝ) (52/100) (413/1000) (565/1000) :=
  geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP_6 (hn : 16384 ≤ n) : GeoP n (52/100 : ℝ) (528/1000) (405/1000) (554/1000) :=
  geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end BstLean.Part186

#print axioms BstLean.Part186.geoP_0

#print axioms BstLean.Part186.geoP_1

#print axioms BstLean.Part186.geoP_2

#print axioms BstLean.Part186.geoP_3

#print axioms BstLean.Part186.geoP_4

#print axioms BstLean.Part186.geoP_5

#print axioms BstLean.Part186.geoP_6
