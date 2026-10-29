import BstLean.Part293Envelope3

namespace BstLean.Part293.Envelope
open Real

noncomputable def v180 (x : ℝ) : ℝ := (v177 x) + (v179 x)

theorem v180_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3421938733608913393 / 1000000000000000000 : ℝ) ≤ v180 x ∧ v180 x ≤ (461779019459572701 / 125000000000000000 : ℝ) := by
  have h177 := v177_bounds x hx0 hx1
  have h179 := v179_bounds x hx0 hx1
  unfold v180
  constructor <;> interval_num

noncomputable def v181 (x : ℝ) : ℝ := (v164 x) ^ 2

theorem v181_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v181 x ∧ v181 x ≤ (528592740747737 / 1000000000000000000 : ℝ) := by
  have h164 := v164_bounds x hx0 hx1
  unfold v181
  constructor <;> interval_num

noncomputable def v182 (x : ℝ) : ℝ := (v13 x) ^ 3

theorem v182_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (23852981211839281 / 1000000000000000000 : ℝ) ≤ v182 x ∧ v182 x ≤ (24956478906311171 / 1000000000000000000 : ℝ) := by
  have h13 := v13_bounds x hx0 hx1
  unfold v182
  constructor <;> interval_num

noncomputable def v183 (x : ℝ) : ℝ := (v181 x) / (v182 x)

theorem v183_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v183 x ∧ v183 x ≤ (554011190522983 / 25000000000000000 : ℝ) := by
  have h181 := v181_bounds x hx0 hx1
  have h182 := v182_bounds x hx0 hx1
  unfold v183
  constructor <;> interval_num

noncomputable def v184 (x : ℝ) : ℝ := (v180 x) + (v183 x)

theorem v184_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (213871170850557087 / 62500000000000000 : ℝ) ≤ v184 x ∧ v184 x ≤ (3716392603297500929 / 1000000000000000000 : ℝ) := by
  have h180 := v180_bounds x hx0 hx1
  have h183 := v183_bounds x hx0 hx1
  unfold v184
  constructor <;> interval_num

noncomputable def v185 (x : ℝ) : ℝ := (v176 x) ^ 3

theorem v185_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v185 x ∧ v185 x ≤ (19115430914557 / 1000000000000000000 : ℝ) := by
  have h176 := v176_bounds x hx0 hx1
  unfold v185
  constructor <;> interval_num

noncomputable def v186 (x : ℝ) : ℝ := (v13 x) ^ 3

theorem v186_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (23852981211839281 / 1000000000000000000 : ℝ) ≤ v186 x ∧ v186 x ≤ (24956478906311171 / 1000000000000000000 : ℝ) := by
  have h13 := v13_bounds x hx0 hx1
  unfold v186
  constructor <;> interval_num

noncomputable def v187 (x : ℝ) : ℝ := (v186 x) * ((17919 / 100000 : ℝ))

theorem v187_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (4274215703349479 / 1000000000000000000 : ℝ) ≤ v187 x ∧ v187 x ≤ (44719514552219 / 10000000000000000 : ℝ) := by
  have h186 := v186_bounds x hx0 hx1
  unfold v187
  constructor <;> interval_num

noncomputable def v188 (x : ℝ) : ℝ := (v185 x) / (v187 x)

theorem v188_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v188 x ∧ v188 x ≤ (89445326306659 / 20000000000000000 : ℝ) := by
  have h185 := v185_bounds x hx0 hx1
  have h187 := v187_bounds x hx0 hx1
  unfold v188
  constructor <;> interval_num

noncomputable def v189 (x : ℝ) : ℝ := (v184 x) + (v188 x)

theorem v189_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3421938733608913391 / 1000000000000000000 : ℝ) ≤ v189 x ∧ v189 x ≤ (93021621740320847 / 25000000000000000 : ℝ) := by
  have h184 := v184_bounds x hx0 hx1
  have h188 := v188_bounds x hx0 hx1
  unfold v189
  constructor <;> interval_num

noncomputable def v190 (x : ℝ) : ℝ := (v26 x) * ((2 : ℝ))

theorem v190_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v190 x ∧ v190 x ≤ (7236928183426259 / 1000000000000000000 : ℝ) := by
  have h26 := v26_bounds x hx0 hx1
  unfold v190
  constructor <;> interval_num

noncomputable def v191 (x : ℝ) : ℝ := √((9 / 50 : ℝ))

theorem v191_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (212132034355964257 / 500000000000000000 : ℝ) ≤ v191 x ∧ v191 x ≤ (84852813742385703 / 200000000000000000 : ℝ) := by
  unfold v191
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v192 (x : ℝ) : ℝ := (v190 x) / (v191 x)

theorem v192_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v192 x ∧ v192 x ≤ (17057603311535837 / 1000000000000000000 : ℝ) := by
  have h190 := v190_bounds x hx0 hx1
  have h191 := v191_bounds x hx0 hx1
  unfold v192
  constructor <;> interval_num

noncomputable def v193 (x : ℝ) : ℝ := (v192 x) + ((1 : ℝ))

theorem v193_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v193 x ∧ v193 x ≤ (508528801655767919 / 500000000000000000 : ℝ) := by
  have h192 := v192_bounds x hx0 hx1
  unfold v193
  constructor <;> interval_num

noncomputable def v194 (x : ℝ) : ℝ := (v193 x) ^ 2

theorem v194_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999997 / 1000000000000000000 : ℝ) ≤ v194 x ∧ v194 x ≤ (258601542113451349 / 250000000000000000 : ℝ) := by
  have h193 := v193_bounds x hx0 hx1
  unfold v194
  constructor <;> interval_num

noncomputable def v195 (x : ℝ) : ℝ := (v194 x) - ((1 : ℝ))

theorem v195_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (-1 / 250000000000000000 : ℝ) ≤ v195 x ∧ v195 x ≤ (34406168453805397 / 1000000000000000000 : ℝ) := by
  have h194 := v194_bounds x hx0 hx1
  unfold v195
  constructor <;> interval_num

noncomputable def v196 (x : ℝ) : ℝ := (v195 x) ^ 2

theorem v196_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (-1 / 500000000000000000 : ℝ) ≤ v196 x ∧ v196 x ≤ (236756885534327 / 200000000000000000 : ℝ) := by
  have h195 := v195_bounds x hx0 hx1
  unfold v196
  constructor <;> interval_num

noncomputable def v197 (x : ℝ) : ℝ := ((1 : ℝ)) - (v196 x)

theorem v197_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (249704053893082091 / 250000000000000000 : ℝ) ≤ v197 x ∧ v197 x ≤ (1000000000000000003 / 1000000000000000000 : ℝ) := by
  have h196 := v196_bounds x hx0 hx1
  unfold v197
  constructor <;> interval_num

noncomputable def v198 (x : ℝ) : ℝ := ((1 : ℝ)) / (v197 x)

theorem v198_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (249999999999999999 / 250000000000000000 : ℝ) ≤ v198 x ∧ v198 x ≤ (1001185187434099997 / 1000000000000000000 : ℝ) := by
  have h197 := v197_bounds x hx0 hx1
  unfold v198
  constructor <;> interval_num

noncomputable def v199 (x : ℝ) : ℝ := (v32 x) / ((9 / 50 : ℝ))

theorem v199_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2777777777777777771 / 500000000000000000 : ℝ) ≤ v199 x ∧ v199 x ≤ (3001276852567078801 / 500000000000000000 : ℝ) := by
  have h32 := v32_bounds x hx0 hx1
  unfold v199
  constructor <;> interval_num

noncomputable def v200 (x : ℝ) : ℝ := (v199 x) * ((4 : ℝ))

theorem v200_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (22222222222222222167 / 1000000000000000000 : ℝ) ≤ v200 x ∧ v200 x ≤ (24010214820536630409 / 1000000000000000000 : ℝ) := by
  have h199 := v199_bounds x hx0 hx1
  unfold v200
  constructor <;> interval_num

noncomputable def v201 (x : ℝ) : ℝ := (v200 x) * ((49 / 4 : ℝ))

theorem v201_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (34027777777777777693 / 125000000000000000 : ℝ) ≤ v201 x ∧ v201 x ≤ (18382820721973357657 / 62500000000000000 : ℝ) := by
  have h200 := v200_bounds x hx0 hx1
  unfold v201
  constructor <;> interval_num

noncomputable def v202 (x : ℝ) : ℝ := (v6 x) ^ 2

theorem v202_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v202 x ∧ v202 x ≤ (22416815361443203601 / 1000000000000000000 : ℝ) := by
  have h6 := v6_bounds x hx0 hx1
  unfold v202
  constructor <;> interval_num

noncomputable def v203 (x : ℝ) : ℝ := (v201 x) * (v202 x)

theorem v203_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v203 x ∧ v203 x ≤ (6593348767151820903981 / 1000000000000000000 : ℝ) := by
  have h201 := v201_bounds x hx0 hx1
  have h202 := v202_bounds x hx0 hx1
  unfold v203
  constructor <;> interval_num

noncomputable def v204 (x : ℝ) : ℝ := (v203 x) * ((1521 / 500 : ℝ))

theorem v204_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v204 x ∧ v204 x ≤ (2507120868709479898739 / 125000000000000000 : ℝ) := by
  have h203 := v203_bounds x hx0 hx1
  unfold v204
  constructor <;> interval_num

noncomputable def v205 (x : ℝ) : ℝ := (v204 x) * (v0 x)

theorem v205_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v205 x ∧ v205 x ≤ (25071208687094799 / 10000000000000000 : ℝ) := by
  have h204 := v204_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v205
  constructor <;> interval_num

noncomputable def v206 (x : ℝ) : ℝ := (v0 x) * ((25 : ℝ))

theorem v206_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v206 x ∧ v206 x ≤ (3125000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v206
  constructor <;> interval_num

noncomputable def v207 (x : ℝ) : ℝ := ((1 : ℝ)) - (v206 x)

theorem v207_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (498437499999999999 / 500000000000000000 : ℝ) ≤ v207 x ∧ v207 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h206 := v206_bounds x hx0 hx1
  unfold v207
  constructor <;> interval_num

noncomputable def v208 (x : ℝ) : ℝ := (v205 x) / (v207 x)

theorem v208_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v208 x ∧ v208 x ≤ (502996036355506941 / 200000000000000000 : ℝ) := by
  have h205 := v205_bounds x hx0 hx1
  have h207 := v207_bounds x hx0 hx1
  unfold v208
  constructor <;> interval_num

noncomputable def v209 (x : ℝ) : ℝ := √((9 / 50 : ℝ))

theorem v209_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (212132034355964257 / 500000000000000000 : ℝ) ≤ v209 x ∧ v209 x ≤ (84852813742385703 / 200000000000000000 : ℝ) := by
  unfold v209
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v210 (x : ℝ) : ℝ := (v26 x) / (v209 x)

theorem v210_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v210 x ∧ v210 x ≤ (4264400827883959 / 500000000000000000 : ℝ) := by
  have h26 := v26_bounds x hx0 hx1
  have h209 := v209_bounds x hx0 hx1
  unfold v210
  constructor <;> interval_num

noncomputable def v211 (x : ℝ) : ℝ := (v210 x) + ((1 : ℝ))

theorem v211_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v211 x ∧ v211 x ≤ (1008528801655767919 / 1000000000000000000 : ℝ) := by
  have h210 := v210_bounds x hx0 hx1
  unfold v211
  constructor <;> interval_num

noncomputable def v212 (x : ℝ) : ℝ := (v211 x) ^ 2

theorem v212_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999997 / 1000000000000000000 : ℝ) ≤ v212 x ∧ v212 x ≤ (1017130343769219269 / 1000000000000000000 : ℝ) := by
  have h211 := v211_bounds x hx0 hx1
  unfold v212
  constructor <;> interval_num

noncomputable def v213 (x : ℝ) : ℝ := (v212 x) * ((4 : ℝ))

theorem v213_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3999999999999999987 / 1000000000000000000 : ℝ) ≤ v213 x ∧ v213 x ≤ (4068521375076877077 / 1000000000000000000 : ℝ) := by
  have h212 := v212_bounds x hx0 hx1
  unfold v213
  constructor <;> interval_num

noncomputable def v214 (x : ℝ) : ℝ := (v213 x) / ((1991 / 2000 : ℝ))

theorem v214_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (4018081366147664473 / 1000000000000000000 : ℝ) ≤ v214 x ∧ v214 x ≤ (4086912481242468187 / 1000000000000000000 : ℝ) := by
  have h213 := v213_bounds x hx0 hx1
  unfold v214
  constructor <;> interval_num

noncomputable def v215 (x : ℝ) : ℝ := (v214 x) * (v140 x)

theorem v215_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (6874814130806455803 / 500000000000000000 : ℝ) ≤ v215 x ∧ v215 x ≤ (1901504622888185021 / 125000000000000000 : ℝ) := by
  have h214 := v214_bounds x hx0 hx1
  have h140 := v140_bounds x hx0 hx1
  unfold v215
  constructor <;> interval_num

noncomputable def v216 (x : ℝ) : ℝ := (v215 x) * (v18 x)

theorem v216_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v216 x ∧ v216 x ≤ (361659188651 / 500000000000000000 : ℝ) := by
  have h215 := v215_bounds x hx0 hx1
  have h18 := v18_bounds x hx0 hx1
  unfold v216
  constructor <;> interval_num

noncomputable def v217 (x : ℝ) : ℝ := (v215 x) * ((1521 / 500 : ℝ))

theorem v217_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2614148073239154819 / 62500000000000000 : ℝ) ≤ v217 x ∧ v217 x ≤ (46275016502606870673 / 1000000000000000000 : ℝ) := by
  have h215 := v215_bounds x hx0 hx1
  unfold v217
  constructor <;> interval_num

noncomputable def v218 (x : ℝ) : ℝ := (v217 x) * (v0 x)

theorem v218_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v218 x ∧ v218 x ≤ (289218853141293 / 50000000000000000 : ℝ) := by
  have h217 := v217_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v218
  constructor <;> interval_num

noncomputable def v219 (x : ℝ) : ℝ := (v0 x) * ((3 : ℝ))

theorem v219_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v219 x ∧ v219 x ≤ (375000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v219
  constructor <;> interval_num

noncomputable def v220 (x : ℝ) : ℝ := ((1 : ℝ)) - (v219 x)

theorem v220_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499812499999999999 / 500000000000000000 : ℝ) ≤ v220 x ∧ v220 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h219 := v219_bounds x hx0 hx1
  unfold v220
  constructor <;> interval_num

noncomputable def v221 (x : ℝ) : ℝ := (v218 x) / (v220 x)

theorem v221_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v221 x ∧ v221 x ≤ (1446636754489399 / 250000000000000000 : ℝ) := by
  have h218 := v218_bounds x hx0 hx1
  have h220 := v220_bounds x hx0 hx1
  unfold v221
  constructor <;> interval_num

noncomputable def v222 (x : ℝ) : ℝ := (v32 x) / ((1991 / 2000 : ℝ))

theorem v222_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (502260170768458059 / 500000000000000000 : ℝ) ≤ v222 x ∧ v222 x ≤ (1085343713635508157 / 1000000000000000000 : ℝ) := by
  have h32 := v32_bounds x hx0 hx1
  unfold v222
  constructor <;> interval_num

noncomputable def v223 (x : ℝ) : ℝ := (v222 x) * (v140 x)

theorem v223_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (34374070654032279 / 10000000000000000 : ℝ) ≤ v223 x ∧ v223 x ≤ (2019897512728860407 / 500000000000000000 : ℝ) := by
  have h222 := v222_bounds x hx0 hx1
  have h140 := v140_bounds x hx0 hx1
  unfold v223
  constructor <;> interval_num

noncomputable def v224 (x : ℝ) : ℝ := (v223 x) * ((1521 / 500 : ℝ))

theorem v224_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1045659229295661927 / 100000000000000000 : ℝ) ≤ v224 x ∧ v224 x ≤ (6144528233721193359 / 500000000000000000 : ℝ) := by
  have h223 := v223_bounds x hx0 hx1
  unfold v224
  constructor <;> interval_num

end BstLean.Part293.Envelope
