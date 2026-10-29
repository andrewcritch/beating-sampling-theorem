import BstLean.Part293Envelope2

namespace BstLean.Part293.Envelope
open Real

noncomputable def v135 (x : ℝ) : ℝ := (v131 x) + (v134 x)

theorem v135_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (213871170850557087 / 62500000000000000 : ℝ) ≤ v135 x ∧ v135 x ≤ (3717612109601833331 / 1000000000000000000 : ℝ) := by
  have h131 := v131_bounds x hx0 hx1
  have h134 := v134_bounds x hx0 hx1
  unfold v135
  constructor <;> interval_num

noncomputable def v136 (x : ℝ) : ℝ := (v127 x) ^ 3

theorem v136_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v136 x ∧ v136 x ≤ (4854009585423 / 250000000000000000 : ℝ) := by
  have h127 := v127_bounds x hx0 hx1
  unfold v136
  constructor <;> interval_num

noncomputable def v137 (x : ℝ) : ℝ := (v13 x) ^ 3

theorem v137_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (23852981211839281 / 1000000000000000000 : ℝ) ≤ v137 x ∧ v137 x ≤ (24956478906311171 / 1000000000000000000 : ℝ) := by
  have h13 := v13_bounds x hx0 hx1
  unfold v137
  constructor <;> interval_num

noncomputable def v138 (x : ℝ) : ℝ := (v137 x) * ((9 / 50 : ℝ))

theorem v138_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (4293536618131069 / 1000000000000000000 : ℝ) ≤ v138 x ∧ v138 x ≤ (1123041550784003 / 250000000000000000 : ℝ) := by
  have h137 := v137_bounds x hx0 hx1
  unfold v138
  constructor <;> interval_num

noncomputable def v139 (x : ℝ) : ℝ := (v136 x) / (v138 x)

theorem v139_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v139 x ∧ v139 x ≤ (282634691231299 / 62500000000000000 : ℝ) := by
  have h136 := v136_bounds x hx0 hx1
  have h138 := v138_bounds x hx0 hx1
  unfold v139
  constructor <;> interval_num

noncomputable def v140 (x : ℝ) : ℝ := (v135 x) + (v139 x)

theorem v140_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3421938733608913391 / 1000000000000000000 : ℝ) ≤ v140 x ∧ v140 x ≤ (930533566165383529 / 250000000000000000 : ℝ) := by
  have h135 := v135_bounds x hx0 hx1
  have h139 := v139_bounds x hx0 hx1
  unfold v140
  constructor <;> interval_num

noncomputable def v141 (x : ℝ) : ℝ := (v7 x) * ((2 : ℝ))

theorem v141_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v141 x ∧ v141 x ≤ (5252121750000003 / 1000000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v141
  constructor <;> interval_num

noncomputable def v142 (x : ℝ) : ℝ := (v11 x) * ((2 : ℝ))

theorem v142_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1682578972886562607 / 1000000000000000000 : ℝ) ≤ v142 x ∧ v142 x ≤ (1687768096126571857 / 1000000000000000000 : ℝ) := by
  have h11 := v11_bounds x hx0 hx1
  unfold v142
  constructor <;> interval_num

noncomputable def v143 (x : ℝ) : ℝ := (v142 x) * (v2 x)

theorem v143_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v143 x ∧ v143 x ≤ (697819351441249639 / 200000000000000000 : ℝ) := by
  have h142 := v142_bounds x hx0 hx1
  have h2 := v2_bounds x hx0 hx1
  unfold v143
  constructor <;> interval_num

noncomputable def v144 (x : ℝ) : ℝ := (v0 x) * ((27323 / 250000 : ℝ))

theorem v144_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v144 x ∧ v144 x ≤ (13661500000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v144
  constructor <;> interval_num

noncomputable def v145 (x : ℝ) : ℝ := √(v144 x)

theorem v145_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v145 x ∧ v145 x ≤ (1848073321056351 / 500000000000000000 : ℝ) := by
  have h144 := v144_bounds x hx0 hx1
  unfold v145
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v146 (x : ℝ) : ℝ := (v143 x) * (v145 x)

theorem v146_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v146 x ∧ v146 x ≤ (12896213263154193 / 1000000000000000000 : ℝ) := by
  have h143 := v143_bounds x hx0 hx1
  have h145 := v145_bounds x hx0 hx1
  unfold v146
  constructor <;> interval_num

noncomputable def v147 (x : ℝ) : ℝ := (v141 x) + (v146 x)

theorem v147_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v147 x ∧ v147 x ≤ (18148335013154197 / 1000000000000000000 : ℝ) := by
  have h141 := v141_bounds x hx0 hx1
  have h146 := v146_bounds x hx0 hx1
  unfold v147
  constructor <;> interval_num

noncomputable def v148 (x : ℝ) : ℝ := (v3 x) ^ 2

theorem v148_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v148 x ∧ v148 x ≤ (7898364572744526401 / 1000000000000000000 : ℝ) := by
  have h3 := v3_bounds x hx0 hx1
  unfold v148
  constructor <;> interval_num

noncomputable def v149 (x : ℝ) : ℝ := (v148 x) * ((27323 / 250000 : ℝ))

theorem v149_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v149 x ∧ v149 x ≤ (863228060884394781 / 1000000000000000000 : ℝ) := by
  have h148 := v148_bounds x hx0 hx1
  unfold v149
  constructor <;> interval_num

noncomputable def v150 (x : ℝ) : ℝ := (v149 x) * (v0 x)

theorem v150_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v150 x ∧ v150 x ≤ (107903507610551 / 1000000000000000000 : ℝ) := by
  have h149 := v149_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v150
  constructor <;> interval_num

noncomputable def v151 (x : ℝ) : ℝ := (v147 x) + (v150 x)

theorem v151_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v151 x ∧ v151 x ≤ (18256238520764749 / 1000000000000000000 : ℝ) := by
  have h147 := v147_bounds x hx0 hx1
  have h150 := v150_bounds x hx0 hx1
  unfold v151
  constructor <;> interval_num

noncomputable def v152 (x : ℝ) : ℝ := (v151 x) + ((0 : ℝ))

theorem v152_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v152 x ∧ v152 x ≤ (73024954083059 / 4000000000000000 : ℝ) := by
  have h151 := v151_bounds x hx0 hx1
  unfold v152
  constructor <;> interval_num

noncomputable def v153 (x : ℝ) : ℝ := (v7 x) * ((2 : ℝ))

theorem v153_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v153 x ∧ v153 x ≤ (5252121750000003 / 1000000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v153
  constructor <;> interval_num

noncomputable def v154 (x : ℝ) : ℝ := (v11 x) * ((2 : ℝ))

theorem v154_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1682578972886562607 / 1000000000000000000 : ℝ) ≤ v154 x ∧ v154 x ≤ (1687768096126571857 / 1000000000000000000 : ℝ) := by
  have h11 := v11_bounds x hx0 hx1
  unfold v154
  constructor <;> interval_num

noncomputable def v155 (x : ℝ) : ℝ := (v154 x) * (v3 x)

theorem v155_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v155 x ∧ v155 x ≤ (2371654192818479119 / 500000000000000000 : ℝ) := by
  have h154 := v154_bounds x hx0 hx1
  have h3 := v3_bounds x hx0 hx1
  unfold v155
  constructor <;> interval_num

noncomputable def v156 (x : ℝ) : ℝ := (v0 x) * ((27323 / 250000 : ℝ))

theorem v156_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v156 x ∧ v156 x ≤ (13661500000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v156
  constructor <;> interval_num

noncomputable def v157 (x : ℝ) : ℝ := √(v156 x)

theorem v157_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v157 x ∧ v157 x ≤ (1848073321056351 / 500000000000000000 : ℝ) := by
  have h156 := v156_bounds x hx0 hx1
  unfold v157
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v158 (x : ℝ) : ℝ := (v155 x) * (v157 x)

theorem v158_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v158 x ∧ v158 x ≤ (8765981681038533 / 500000000000000000 : ℝ) := by
  have h155 := v155_bounds x hx0 hx1
  have h157 := v157_bounds x hx0 hx1
  unfold v158
  constructor <;> interval_num

noncomputable def v159 (x : ℝ) : ℝ := (v153 x) + (v158 x)

theorem v159_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v159 x ∧ v159 x ≤ (2278408511207707 / 100000000000000000 : ℝ) := by
  have h153 := v153_bounds x hx0 hx1
  have h158 := v158_bounds x hx0 hx1
  unfold v159
  constructor <;> interval_num

noncomputable def v160 (x : ℝ) : ℝ := (v5 x) ^ 2

theorem v160_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v160 x ∧ v160 x ≤ (15156441186218404901 / 1000000000000000000 : ℝ) := by
  have h5 := v5_bounds x hx0 hx1
  unfold v160
  constructor <;> interval_num

noncomputable def v161 (x : ℝ) : ℝ := (v160 x) * ((27323 / 250000 : ℝ))

theorem v161_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v161 x ∧ v161 x ≤ (165647777012418191 / 100000000000000000 : ℝ) := by
  have h160 := v160_bounds x hx0 hx1
  unfold v161
  constructor <;> interval_num

noncomputable def v162 (x : ℝ) : ℝ := (v161 x) * (v0 x)

theorem v162_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v162 x ∧ v162 x ≤ (51764930316381 / 250000000000000000 : ℝ) := by
  have h161 := v161_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v162
  constructor <;> interval_num

noncomputable def v163 (x : ℝ) : ℝ := (v159 x) + (v162 x)

theorem v163_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v163 x ∧ v163 x ≤ (4598228966668519 / 200000000000000000 : ℝ) := by
  have h159 := v159_bounds x hx0 hx1
  have h162 := v162_bounds x hx0 hx1
  unfold v163
  constructor <;> interval_num

noncomputable def v164 (x : ℝ) : ℝ := (v163 x) + ((0 : ℝ))

theorem v164_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v164 x ∧ v164 x ≤ (5747786208335649 / 250000000000000000 : ℝ) := by
  have h163 := v163_bounds x hx0 hx1
  unfold v164
  constructor <;> interval_num

noncomputable def v165 (x : ℝ) : ℝ := (v7 x) * ((2 : ℝ))

theorem v165_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v165 x ∧ v165 x ≤ (5252121750000003 / 1000000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v165
  constructor <;> interval_num

noncomputable def v166 (x : ℝ) : ℝ := (v11 x) * ((2 : ℝ))

theorem v166_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1682578972886562607 / 1000000000000000000 : ℝ) ≤ v166 x ∧ v166 x ≤ (1687768096126571857 / 1000000000000000000 : ℝ) := by
  have h11 := v11_bounds x hx0 hx1
  unfold v166
  constructor <;> interval_num

noncomputable def v167 (x : ℝ) : ℝ := (v166 x) * (v4 x)

theorem v167_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v167 x ∧ v167 x ≤ (2865088740065247727 / 500000000000000000 : ℝ) := by
  have h166 := v166_bounds x hx0 hx1
  have h4 := v4_bounds x hx0 hx1
  unfold v167
  constructor <;> interval_num

noncomputable def v168 (x : ℝ) : ℝ := (v0 x) * ((27323 / 250000 : ℝ))

theorem v168_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v168 x ∧ v168 x ≤ (13661500000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v168
  constructor <;> interval_num

noncomputable def v169 (x : ℝ) : ℝ := √(v168 x)

theorem v169_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v169 x ∧ v169 x ≤ (1848073321056351 / 500000000000000000 : ℝ) := by
  have h168 := v168_bounds x hx0 hx1
  unfold v169
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v170 (x : ℝ) : ℝ := (v167 x) * (v169 x)

theorem v170_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v170 x ∧ v170 x ≤ (5294894062973539 / 250000000000000000 : ℝ) := by
  have h167 := v167_bounds x hx0 hx1
  have h169 := v169_bounds x hx0 hx1
  unfold v170
  constructor <;> interval_num

noncomputable def v171 (x : ℝ) : ℝ := (v165 x) + (v170 x)

theorem v171_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v171 x ∧ v171 x ≤ (330396225023677 / 12500000000000000 : ℝ) := by
  have h165 := v165_bounds x hx0 hx1
  have h170 := v170_bounds x hx0 hx1
  unfold v171
  constructor <;> interval_num

noncomputable def v172 (x : ℝ) : ℝ := (v6 x) ^ 2

theorem v172_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v172 x ∧ v172 x ≤ (22416815361443203601 / 1000000000000000000 : ℝ) := by
  have h6 := v6_bounds x hx0 hx1
  unfold v172
  constructor <;> interval_num

noncomputable def v173 (x : ℝ) : ℝ := (v172 x) * ((27323 / 250000 : ℝ))

theorem v173_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v173 x ∧ v173 x ≤ (2449978584482850609 / 1000000000000000000 : ℝ) := by
  have h172 := v172_bounds x hx0 hx1
  unfold v173
  constructor <;> interval_num

noncomputable def v174 (x : ℝ) : ℝ := (v173 x) * (v0 x)

theorem v174_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v174 x ∧ v174 x ≤ (153123661530179 / 500000000000000000 : ℝ) := by
  have h173 := v173_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v174
  constructor <;> interval_num

noncomputable def v175 (x : ℝ) : ℝ := (v171 x) + (v174 x)

theorem v175_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v175 x ∧ v175 x ≤ (26737945324954519 / 1000000000000000000 : ℝ) := by
  have h171 := v171_bounds x hx0 hx1
  have h174 := v174_bounds x hx0 hx1
  unfold v175
  constructor <;> interval_num

noncomputable def v176 (x : ℝ) : ℝ := (v175 x) + ((0 : ℝ))

theorem v176_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v176 x ∧ v176 x ≤ (668448633123863 / 25000000000000000 : ℝ) := by
  have h175 := v175_bounds x hx0 hx1
  unfold v176
  constructor <;> interval_num

noncomputable def v177 (x : ℝ) : ℝ := ((1 : ℝ)) / (v13 x)

theorem v177_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1710969366804456697 / 500000000000000000 : ℝ) ≤ v177 x ∧ v177 x ≤ (1736957193669443181 / 500000000000000000 : ℝ) := by
  have h13 := v13_bounds x hx0 hx1
  unfold v177
  constructor <;> interval_num

noncomputable def v178 (x : ℝ) : ℝ := (v13 x) ^ 2

theorem v178_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (41431607306366313 / 500000000000000000 : ℝ) ≤ v178 x ∧ v178 x ≤ (17079908364800001 / 200000000000000000 : ℝ) := by
  have h13 := v13_bounds x hx0 hx1
  unfold v178
  constructor <;> interval_num

noncomputable def v179 (x : ℝ) : ℝ := (v152 x) / (v178 x)

theorem v179_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v179 x ∧ v179 x ≤ (44063553667539049 / 200000000000000000 : ℝ) := by
  have h152 := v152_bounds x hx0 hx1
  have h178 := v178_bounds x hx0 hx1
  unfold v179
  constructor <;> interval_num

end BstLean.Part293.Envelope
