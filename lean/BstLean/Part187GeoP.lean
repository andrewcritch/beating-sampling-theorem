import BstLean.Part187CovC

/-!
# Part 187 (file `GeoP`): the core window geometry of the seven θ-pieces at `n ≥ 16 250`

No proof is left open; no `native_decide` or `axiom` is used. Windows (core pairs `Γ(3.75, 7, 3.75)`,
`1/√n ≤ 1/127`): `[0.463, 0.615]`, `[0.453, 0.605]`, `[0.443, 0.595]`, `[0.433, 0.585]`, `[0.423, 0.575]`,
`[0.413, 0.565]`, `[0.405, 0.555]` for the pieces `[0.46, 0.47]`, …, `[0.52, 0.528]`.
-/

namespace BstLean.Part187

variable {n : ℕ}

theorem geoP16250_0 (hn : 16250 ≤ n) : BstLean.Part186.GeoP n (46/100 : ℝ) (47/100) (463/1000) (615/1000) :=
  BstLean.Part186.R16250.geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP16250_1 (hn : 16250 ≤ n) : BstLean.Part186.GeoP n (47/100 : ℝ) (48/100) (453/1000) (605/1000) :=
  BstLean.Part186.R16250.geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP16250_2 (hn : 16250 ≤ n) : BstLean.Part186.GeoP n (48/100 : ℝ) (49/100) (443/1000) (595/1000) :=
  BstLean.Part186.R16250.geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP16250_3 (hn : 16250 ≤ n) : BstLean.Part186.GeoP n (49/100 : ℝ) (50/100) (433/1000) (585/1000) :=
  BstLean.Part186.R16250.geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP16250_4 (hn : 16250 ≤ n) : BstLean.Part186.GeoP n (50/100 : ℝ) (51/100) (423/1000) (575/1000) :=
  BstLean.Part186.R16250.geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP16250_5 (hn : 16250 ≤ n) : BstLean.Part186.GeoP n (51/100 : ℝ) (52/100) (413/1000) (565/1000) :=
  BstLean.Part186.R16250.geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem geoP16250_6 (hn : 16250 ≤ n) : BstLean.Part186.GeoP n (52/100 : ℝ) (528/1000) (405/1000) (555/1000) :=
  BstLean.Part186.R16250.geoP hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end BstLean.Part187
