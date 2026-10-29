import BstLean.Part228Arithmetic

/-! Normalized scalar formulas on the entire low band. -/
namespace BstLean.Part292
open Real

noncomputable def lowScalar0 (x : ℝ) : ℝ := x

noncomputable def lowScalar1 (x : ℝ) : ℝ := sqrt (lowScalar0 x)

noncomputable def lowScalar2 (x : ℝ) : ℝ := (517 / 200 : ℝ)

noncomputable def lowScalar3 (x : ℝ) : ℝ := (27 / 50 : ℝ)

noncomputable def lowScalar4 (x : ℝ) : ℝ := sqrt (lowScalar3 x)

noncomputable def lowScalar5 (x : ℝ) : ℝ := (23 / 50 : ℝ)

noncomputable def lowScalar6 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar5 x)

noncomputable def lowScalar7 (x : ℝ) : ℝ := sqrt (lowScalar6 x)

noncomputable def lowScalar8 (x : ℝ) : ℝ := (6 / 1 : ℝ)

noncomputable def lowScalar9 (x : ℝ) : ℝ := (lowScalar7 x) * (lowScalar8 x)

noncomputable def lowScalar10 (x : ℝ) : ℝ := (lowScalar4 x) + (lowScalar9 x)

noncomputable def lowScalar11 (x : ℝ) : ℝ := (lowScalar10 x) ^ 2

noncomputable def lowScalar12 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar13 (x : ℝ) : ℝ := -(lowScalar11 x)

noncomputable def lowScalar14 (x : ℝ) : ℝ := (lowScalar12 x) + (lowScalar13 x)

noncomputable def lowScalar15 (x : ℝ) : ℝ := (23 / 50 : ℝ)

noncomputable def lowScalar16 (x : ℝ) : ℝ := sqrt (lowScalar15 x)

noncomputable def lowScalar17 (x : ℝ) : ℝ := (27 / 50 : ℝ)

noncomputable def lowScalar18 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar17 x)

noncomputable def lowScalar19 (x : ℝ) : ℝ := sqrt (lowScalar18 x)

noncomputable def lowScalar20 (x : ℝ) : ℝ := (6 / 1 : ℝ)

noncomputable def lowScalar21 (x : ℝ) : ℝ := (lowScalar19 x) * (lowScalar20 x)

noncomputable def lowScalar22 (x : ℝ) : ℝ := -(lowScalar21 x)

noncomputable def lowScalar23 (x : ℝ) : ℝ := (lowScalar16 x) + (lowScalar22 x)

noncomputable def lowScalar24 (x : ℝ) : ℝ := (lowScalar23 x) ^ 2

noncomputable def lowScalar25 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar26 (x : ℝ) : ℝ := -(lowScalar24 x)

noncomputable def lowScalar27 (x : ℝ) : ℝ := (lowScalar25 x) + (lowScalar26 x)

noncomputable def lowScalar28 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar29 (x : ℝ) : ℝ := (lowScalar1 x) + (lowScalar28 x)

noncomputable def lowScalar30 (x : ℝ) : ℝ := (6 / 1 : ℝ)

noncomputable def lowScalar31 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar30 x)

noncomputable def lowScalar32 (x : ℝ) : ℝ := (lowScalar29 x) + (lowScalar31 x)

noncomputable def lowScalar33 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar34 (x : ℝ) : ℝ := (lowScalar32 x) * (lowScalar33 x)

noncomputable def lowScalar35 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar36 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar35 x)

noncomputable def lowScalar37 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar38 (x : ℝ) : ℝ := -(lowScalar36 x)

noncomputable def lowScalar39 (x : ℝ) : ℝ := (lowScalar37 x) + (lowScalar38 x)

noncomputable def lowScalar40 (x : ℝ) : ℝ := sqrt (lowScalar39 x)

noncomputable def lowScalar41 (x : ℝ) : ℝ := 1 / (lowScalar40 x)

noncomputable def lowScalar42 (x : ℝ) : ℝ := (lowScalar34 x) * (lowScalar41 x)

noncomputable def lowScalar43 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar44 (x : ℝ) : ℝ := -(lowScalar0 x)

noncomputable def lowScalar45 (x : ℝ) : ℝ := (lowScalar43 x) + (lowScalar44 x)

noncomputable def lowScalar46 (x : ℝ) : ℝ := sqrt (lowScalar45 x)

noncomputable def lowScalar47 (x : ℝ) : ℝ := (6 / 1 : ℝ)

noncomputable def lowScalar48 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar47 x)

noncomputable def lowScalar49 (x : ℝ) : ℝ := (lowScalar48 x) * (lowScalar1 x)

noncomputable def lowScalar50 (x : ℝ) : ℝ := (lowScalar46 x) + (lowScalar49 x)

noncomputable def lowScalar51 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar52 (x : ℝ) : ℝ := (lowScalar50 x) * (lowScalar51 x)

noncomputable def lowScalar53 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar54 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar53 x)

noncomputable def lowScalar55 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar56 (x : ℝ) : ℝ := -(lowScalar54 x)

noncomputable def lowScalar57 (x : ℝ) : ℝ := (lowScalar55 x) + (lowScalar56 x)

noncomputable def lowScalar58 (x : ℝ) : ℝ := sqrt (lowScalar57 x)

noncomputable def lowScalar59 (x : ℝ) : ℝ := 1 / (lowScalar58 x)

noncomputable def lowScalar60 (x : ℝ) : ℝ := (lowScalar52 x) * (lowScalar59 x)

noncomputable def lowScalar61 (x : ℝ) : ℝ := (6 / 1 : ℝ)

noncomputable def lowScalar62 (x : ℝ) : ℝ := sqrt (lowScalar61 x)

noncomputable def lowScalar63 (x : ℝ) : ℝ := (lowScalar62 x) * (lowScalar0 x)

noncomputable def lowScalar64 (x : ℝ) : ℝ := (1 / 2 : ℝ)

noncomputable def lowScalar65 (x : ℝ) : ℝ := -(lowScalar63 x)

noncomputable def lowScalar66 (x : ℝ) : ℝ := (lowScalar64 x) + (lowScalar65 x)

noncomputable def lowScalar67 (x : ℝ) : ℝ := (12 / 1 : ℝ)

noncomputable def lowScalar68 (x : ℝ) : ℝ := (lowScalar66 x) * (lowScalar67 x)

noncomputable def lowScalar69 (x : ℝ) : ℝ := sqrt (lowScalar68 x)

noncomputable def lowScalar70 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar71 (x : ℝ) : ℝ := (lowScalar69 x) * (lowScalar70 x)

noncomputable def lowScalar72 (x : ℝ) : ℝ := (lowScalar71 x) * (lowScalar0 x)

noncomputable def lowScalar73 (x : ℝ) : ℝ := (lowScalar72 x) * (lowScalar1 x)

noncomputable def lowScalar74 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar75 (x : ℝ) : ℝ := -(lowScalar0 x)

noncomputable def lowScalar76 (x : ℝ) : ℝ := (lowScalar74 x) + (lowScalar75 x)

noncomputable def lowScalar77 (x : ℝ) : ℝ := sqrt (lowScalar76 x)

noncomputable def lowScalar78 (x : ℝ) : ℝ := 1 / (lowScalar77 x)

noncomputable def lowScalar79 (x : ℝ) : ℝ := (lowScalar73 x) * (lowScalar78 x)

noncomputable def lowScalar80 (x : ℝ) : ℝ := -(lowScalar79 x)

noncomputable def lowScalar81 (x : ℝ) : ℝ := (lowScalar66 x) + (lowScalar80 x)

noncomputable def lowScalar82 (x : ℝ) : ℝ := sqrt (lowScalar81 x)

noncomputable def lowScalar83 (x : ℝ) : ℝ := (4 / 1 : ℝ)

noncomputable def lowScalar84 (x : ℝ) : ℝ := (lowScalar2 x) * (lowScalar83 x)

noncomputable def lowScalar85 (x : ℝ) : ℝ := (3 / 1 : ℝ)

noncomputable def lowScalar86 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar85 x)

noncomputable def lowScalar87 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar88 (x : ℝ) : ℝ := -(lowScalar86 x)

noncomputable def lowScalar89 (x : ℝ) : ℝ := (lowScalar87 x) + (lowScalar88 x)

noncomputable def lowScalar90 (x : ℝ) : ℝ := 1 / (lowScalar89 x)

noncomputable def lowScalar91 (x : ℝ) : ℝ := (lowScalar84 x) * (lowScalar90 x)

noncomputable def lowScalar92 (x : ℝ) : ℝ := (16 / 1 : ℝ)

noncomputable def lowScalar93 (x : ℝ) : ℝ := (lowScalar2 x) * (lowScalar92 x)

noncomputable def lowScalar94 (x : ℝ) : ℝ := (3 / 1 : ℝ)

noncomputable def lowScalar95 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar94 x)

noncomputable def lowScalar96 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar97 (x : ℝ) : ℝ := -(lowScalar95 x)

noncomputable def lowScalar98 (x : ℝ) : ℝ := (lowScalar96 x) + (lowScalar97 x)

noncomputable def lowScalar99 (x : ℝ) : ℝ := 1 / (lowScalar98 x)

noncomputable def lowScalar100 (x : ℝ) : ℝ := (lowScalar93 x) * (lowScalar99 x)

noncomputable def lowScalar101 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar102 (x : ℝ) : ℝ := (lowScalar1 x) + (lowScalar101 x)

noncomputable def lowScalar103 (x : ℝ) : ℝ := (6 / 1 : ℝ)

noncomputable def lowScalar104 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar103 x)

noncomputable def lowScalar105 (x : ℝ) : ℝ := (lowScalar102 x) + (lowScalar104 x)

noncomputable def lowScalar106 (x : ℝ) : ℝ := (lowScalar105 x) ^ 2

noncomputable def lowScalar107 (x : ℝ) : ℝ := (4 / 1 : ℝ)

noncomputable def lowScalar108 (x : ℝ) : ℝ := (lowScalar106 x) * (lowScalar107 x)

noncomputable def lowScalar109 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar110 (x : ℝ) : ℝ := 1 / (lowScalar109 x)

noncomputable def lowScalar111 (x : ℝ) : ℝ := (lowScalar81 x) * (lowScalar110 x)

noncomputable def lowScalar112 (x : ℝ) : ℝ := (lowScalar42 x) ^ 2

noncomputable def lowScalar113 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar114 (x : ℝ) : ℝ := (lowScalar112 x) * (lowScalar113 x)

noncomputable def lowScalar115 (x : ℝ) : ℝ := (lowScalar114 x) * (lowScalar0 x)

noncomputable def lowScalar116 (x : ℝ) : ℝ := -(lowScalar115 x)

noncomputable def lowScalar117 (x : ℝ) : ℝ := (lowScalar111 x) + (lowScalar116 x)

noncomputable def lowScalar118 (x : ℝ) : ℝ := (5623 / 2000 : ℝ)

noncomputable def lowScalar119 (x : ℝ) : ℝ := (lowScalar118 x) ^ 8

noncomputable def lowScalar120 (x : ℝ) : ℝ := (16 / 1 : ℝ)

noncomputable def lowScalar121 (x : ℝ) : ℝ := (lowScalar2 x) * (lowScalar120 x)

noncomputable def lowScalar122 (x : ℝ) : ℝ := (lowScalar121 x) ^ 4

noncomputable def lowScalar123 (x : ℝ) : ℝ := (lowScalar119 x) * (lowScalar122 x)

noncomputable def lowScalar124 (x : ℝ) : ℝ := (3 / 1 : ℝ)

noncomputable def lowScalar125 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar124 x)

noncomputable def lowScalar126 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar127 (x : ℝ) : ℝ := -(lowScalar125 x)

noncomputable def lowScalar128 (x : ℝ) : ℝ := (lowScalar126 x) + (lowScalar127 x)

noncomputable def lowScalar129 (x : ℝ) : ℝ := (5 / 1 : ℝ)

noncomputable def lowScalar130 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar129 x)

noncomputable def lowScalar131 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar132 (x : ℝ) : ℝ := -(lowScalar130 x)

noncomputable def lowScalar133 (x : ℝ) : ℝ := (lowScalar131 x) + (lowScalar132 x)

noncomputable def lowScalar134 (x : ℝ) : ℝ := (lowScalar128 x) * (lowScalar133 x)

noncomputable def lowScalar135 (x : ℝ) : ℝ := (7 / 1 : ℝ)

noncomputable def lowScalar136 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar135 x)

noncomputable def lowScalar137 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar138 (x : ℝ) : ℝ := -(lowScalar136 x)

noncomputable def lowScalar139 (x : ℝ) : ℝ := (lowScalar137 x) + (lowScalar138 x)

noncomputable def lowScalar140 (x : ℝ) : ℝ := (lowScalar134 x) * (lowScalar139 x)

noncomputable def lowScalar141 (x : ℝ) : ℝ := (9 / 1 : ℝ)

noncomputable def lowScalar142 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar141 x)

noncomputable def lowScalar143 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar144 (x : ℝ) : ℝ := -(lowScalar142 x)

noncomputable def lowScalar145 (x : ℝ) : ℝ := (lowScalar143 x) + (lowScalar144 x)

noncomputable def lowScalar146 (x : ℝ) : ℝ := (lowScalar140 x) * (lowScalar145 x)

noncomputable def lowScalar147 (x : ℝ) : ℝ := (lowScalar117 x) ^ 8

noncomputable def lowScalar148 (x : ℝ) : ℝ := (lowScalar146 x) * (lowScalar147 x)

noncomputable def lowScalar149 (x : ℝ) : ℝ := 1 / (lowScalar148 x)

noncomputable def lowScalar150 (x : ℝ) : ℝ := (lowScalar123 x) * (lowScalar149 x)

noncomputable def lowScalar151 (x : ℝ) : ℝ := (132 / 5 : ℝ)

noncomputable def lowScalar152 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar151 x)

noncomputable def lowScalar153 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar154 (x : ℝ) : ℝ := -(lowScalar152 x)

noncomputable def lowScalar155 (x : ℝ) : ℝ := (lowScalar153 x) + (lowScalar154 x)

noncomputable def lowScalar156 (x : ℝ) : ℝ := (66 / 125 : ℝ)

noncomputable def lowScalar157 (x : ℝ) : ℝ := 1 / (lowScalar155 x)

noncomputable def lowScalar158 (x : ℝ) : ℝ := (lowScalar156 x) * (lowScalar157 x)

noncomputable def lowScalar159 (x : ℝ) : ℝ := (45 / 1 : ℝ)

noncomputable def lowScalar160 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar159 x)

noncomputable def lowScalar161 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar162 (x : ℝ) : ℝ := (lowScalar160 x) + (lowScalar161 x)

noncomputable def lowScalar163 (x : ℝ) : ℝ := (lowScalar158 x) * (lowScalar162 x)

noncomputable def lowScalar164 (x : ℝ) : ℝ := (27 / 50 : ℝ)

noncomputable def lowScalar165 (x : ℝ) : ℝ := (lowScalar0 x) * (lowScalar164 x)

noncomputable def lowScalar166 (x : ℝ) : ℝ := sqrt (lowScalar165 x)

noncomputable def lowScalar167 (x : ℝ) : ℝ := (12 / 1 : ℝ)

noncomputable def lowScalar168 (x : ℝ) : ℝ := (lowScalar166 x) * (lowScalar167 x)

noncomputable def lowScalar169 (x : ℝ) : ℝ := (lowScalar168 x) * (lowScalar0 x)

noncomputable def lowScalar170 (x : ℝ) : ℝ := (512 / 1 : ℝ)

noncomputable def lowScalar171 (x : ℝ) : ℝ := 1 / (lowScalar170 x)

noncomputable def lowScalar172 (x : ℝ) : ℝ := (lowScalar169 x) * (lowScalar171 x)

noncomputable def lowScalar173 (x : ℝ) : ℝ := 1 / (lowScalar14 x)

noncomputable def lowScalar174 (x : ℝ) : ℝ := (lowScalar172 x) * (lowScalar173 x)

noncomputable def lowScalar175 (x : ℝ) : ℝ := (1 / 1 : ℝ)

noncomputable def lowScalar176 (x : ℝ) : ℝ := (lowScalar174 x) + (lowScalar175 x)

noncomputable def lowScalar177 (x : ℝ) : ℝ := (lowScalar163 x) * (lowScalar176 x)

noncomputable def lowScalar178 (x : ℝ) : ℝ := (7979 / 20000 : ℝ)

noncomputable def lowScalar179 (x : ℝ) : ℝ := (12099 / 50000 : ℝ)

noncomputable def lowScalar180 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar181 (x : ℝ) : ℝ := sqrt (lowScalar180 x)

noncomputable def lowScalar182 (x : ℝ) : ℝ := (lowScalar178 x) * (lowScalar91 x)

noncomputable def lowScalar183 (x : ℝ) : ℝ := sqrt (lowScalar27 x)

noncomputable def lowScalar184 (x : ℝ) : ℝ := (lowScalar182 x) * (lowScalar183 x)

noncomputable def lowScalar185 (x : ℝ) : ℝ := (lowScalar184 x) * (lowScalar0 x)

noncomputable def lowScalar186 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar187 (x : ℝ) : ℝ := (lowScalar82 x) * (lowScalar186 x)

noncomputable def lowScalar188 (x : ℝ) : ℝ := 1 / (lowScalar187 x)

noncomputable def lowScalar189 (x : ℝ) : ℝ := (lowScalar185 x) * (lowScalar188 x)

noncomputable def lowScalar190 (x : ℝ) : ℝ := (lowScalar178 x) * (lowScalar0 x)

noncomputable def lowScalar191 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar192 (x : ℝ) : ℝ := (lowScalar181 x) * (lowScalar191 x)

noncomputable def lowScalar193 (x : ℝ) : ℝ := (lowScalar82 x) ^ 3

noncomputable def lowScalar194 (x : ℝ) : ℝ := (lowScalar192 x) * (lowScalar193 x)

noncomputable def lowScalar195 (x : ℝ) : ℝ := 1 / (lowScalar194 x)

noncomputable def lowScalar196 (x : ℝ) : ℝ := (lowScalar190 x) * (lowScalar195 x)

noncomputable def lowScalar197 (x : ℝ) : ℝ := sqrt (lowScalar14 x)

noncomputable def lowScalar198 (x : ℝ) : ℝ := 1 / (lowScalar197 x)

noncomputable def lowScalar199 (x : ℝ) : ℝ := (lowScalar100 x) * (lowScalar198 x)

noncomputable def lowScalar200 (x : ℝ) : ℝ := (lowScalar91 x) * (lowScalar91 x)

noncomputable def lowScalar201 (x : ℝ) : ℝ := sqrt (lowScalar27 x)

noncomputable def lowScalar202 (x : ℝ) : ℝ := (lowScalar200 x) * (lowScalar201 x)

noncomputable def lowScalar203 (x : ℝ) : ℝ := (lowScalar202 x) * (lowScalar0 x)

noncomputable def lowScalar204 (x : ℝ) : ℝ := (lowScalar199 x) + (lowScalar203 x)

noncomputable def lowScalar205 (x : ℝ) : ℝ := (lowScalar196 x) * (lowScalar204 x)

noncomputable def lowScalar206 (x : ℝ) : ℝ := (lowScalar189 x) + (lowScalar205 x)

noncomputable def lowScalar207 (x : ℝ) : ℝ := (lowScalar179 x) * (lowScalar0 x)

noncomputable def lowScalar208 (x : ℝ) : ℝ := 1 / (lowScalar81 x)

noncomputable def lowScalar209 (x : ℝ) : ℝ := (lowScalar207 x) * (lowScalar208 x)

noncomputable def lowScalar210 (x : ℝ) : ℝ := (lowScalar91 x) * (lowScalar100 x)

noncomputable def lowScalar211 (x : ℝ) : ℝ := sqrt (lowScalar210 x)

noncomputable def lowScalar212 (x : ℝ) : ℝ := sqrt (lowScalar91 x)

noncomputable def lowScalar213 (x : ℝ) : ℝ := (lowScalar91 x) * (lowScalar212 x)

noncomputable def lowScalar214 (x : ℝ) : ℝ := sqrt (lowScalar27 x)

noncomputable def lowScalar215 (x : ℝ) : ℝ := (lowScalar213 x) * (lowScalar214 x)

noncomputable def lowScalar216 (x : ℝ) : ℝ := (lowScalar215 x) * (lowScalar0 x)

noncomputable def lowScalar217 (x : ℝ) : ℝ := (lowScalar211 x) + (lowScalar216 x)

noncomputable def lowScalar218 (x : ℝ) : ℝ := (lowScalar209 x) * (lowScalar217 x)

noncomputable def lowScalar219 (x : ℝ) : ℝ := (lowScalar178 x) * (lowScalar91 x)

noncomputable def lowScalar220 (x : ℝ) : ℝ := sqrt (lowScalar27 x)

noncomputable def lowScalar221 (x : ℝ) : ℝ := (lowScalar219 x) * (lowScalar220 x)

noncomputable def lowScalar222 (x : ℝ) : ℝ := (lowScalar221 x) * (lowScalar0 x)

noncomputable def lowScalar223 (x : ℝ) : ℝ := (lowScalar181 x) * (lowScalar82 x)

noncomputable def lowScalar224 (x : ℝ) : ℝ := 1 / (lowScalar223 x)

noncomputable def lowScalar225 (x : ℝ) : ℝ := (lowScalar222 x) * (lowScalar224 x)

noncomputable def lowScalar226 (x : ℝ) : ℝ := (lowScalar91 x) * (lowScalar27 x)

noncomputable def lowScalar227 (x : ℝ) : ℝ := (lowScalar226 x) * (lowScalar0 x)

noncomputable def lowScalar228 (x : ℝ) : ℝ := (lowScalar179 x) * (lowScalar0 x)

noncomputable def lowScalar229 (x : ℝ) : ℝ := (2 / 1 : ℝ)

noncomputable def lowScalar230 (x : ℝ) : ℝ := (lowScalar81 x) * (lowScalar229 x)

noncomputable def lowScalar231 (x : ℝ) : ℝ := 1 / (lowScalar230 x)

noncomputable def lowScalar232 (x : ℝ) : ℝ := (lowScalar228 x) * (lowScalar231 x)

noncomputable def lowScalar233 (x : ℝ) : ℝ := (lowScalar91 x) * (lowScalar91 x)

noncomputable def lowScalar234 (x : ℝ) : ℝ := (lowScalar233 x) * (lowScalar27 x)

noncomputable def lowScalar235 (x : ℝ) : ℝ := (lowScalar234 x) * (lowScalar0 x)

noncomputable def lowScalar236 (x : ℝ) : ℝ := (lowScalar100 x) + (lowScalar235 x)

noncomputable def lowScalar237 (x : ℝ) : ℝ := (lowScalar232 x) * (lowScalar236 x)

noncomputable def lowScalar238 (x : ℝ) : ℝ := (lowScalar227 x) + (lowScalar237 x)

noncomputable def lowScalar239 (x : ℝ) : ℝ := (lowScalar181 x) * (lowScalar178 x)

noncomputable def lowScalar240 (x : ℝ) : ℝ := (lowScalar239 x) * (lowScalar0 x)

noncomputable def lowScalar241 (x : ℝ) : ℝ := 1 / (lowScalar82 x)

noncomputable def lowScalar242 (x : ℝ) : ℝ := (lowScalar240 x) * (lowScalar241 x)

noncomputable def lowScalar243 (x : ℝ) : ℝ := (lowScalar91 x) * (lowScalar100 x)

noncomputable def lowScalar244 (x : ℝ) : ℝ := sqrt (lowScalar243 x)

noncomputable def lowScalar245 (x : ℝ) : ℝ := sqrt (lowScalar27 x)

noncomputable def lowScalar246 (x : ℝ) : ℝ := (lowScalar244 x) * (lowScalar245 x)

noncomputable def lowScalar247 (x : ℝ) : ℝ := sqrt (lowScalar91 x)

noncomputable def lowScalar248 (x : ℝ) : ℝ := (lowScalar91 x) * (lowScalar247 x)

noncomputable def lowScalar249 (x : ℝ) : ℝ := (lowScalar248 x) * (lowScalar27 x)

noncomputable def lowScalar250 (x : ℝ) : ℝ := (lowScalar249 x) * (lowScalar0 x)

noncomputable def lowScalar251 (x : ℝ) : ℝ := (lowScalar246 x) + (lowScalar250 x)

noncomputable def lowScalar252 (x : ℝ) : ℝ := (lowScalar242 x) * (lowScalar251 x)

noncomputable def lowScalar253 (x : ℝ) : ℝ := (lowScalar91 x) * (lowScalar27 x)

noncomputable def lowScalar254 (x : ℝ) : ℝ := (lowScalar253 x) * (lowScalar0 x)

noncomputable def lowScalar255 (x : ℝ) : ℝ := (lowScalar0 x) ^ 7

noncomputable def lowScalar256 (x : ℝ) : ℝ := (lowScalar150 x) * (lowScalar255 x)

noncomputable def lowScalar257 (x : ℝ) : ℝ := (lowScalar14 x) ^ 4

noncomputable def lowScalar258 (x : ℝ) : ℝ := 1 / (lowScalar257 x)

noncomputable def lowScalar259 (x : ℝ) : ℝ := (lowScalar256 x) * (lowScalar258 x)

noncomputable def lowScalar260 (x : ℝ) : ℝ := (3 / 2 : ℝ)

noncomputable def lowScalar261 (x : ℝ) : ℝ := (lowScalar178 x) * (lowScalar260 x)

noncomputable def lowScalar262 (x : ℝ) : ℝ := (7 / 1 : ℝ)

noncomputable def lowScalar263 (x : ℝ) : ℝ := (lowScalar261 x) * (lowScalar262 x)

noncomputable def lowScalar264 (x : ℝ) : ℝ := (lowScalar263 x) * (lowScalar259 x)

noncomputable def lowScalar265 (x : ℝ) : ℝ := sqrt (lowScalar14 x)

noncomputable def lowScalar266 (x : ℝ) : ℝ := (lowScalar82 x) * (lowScalar265 x)

noncomputable def lowScalar267 (x : ℝ) : ℝ := 1 / (lowScalar266 x)

noncomputable def lowScalar268 (x : ℝ) : ℝ := (lowScalar264 x) * (lowScalar267 x)

noncomputable def lowScalar269 (x : ℝ) : ℝ := (12 / 1 : ℝ)

noncomputable def lowScalar270 (x : ℝ) : ℝ := (lowScalar181 x) * (lowScalar269 x)

noncomputable def lowScalar271 (x : ℝ) : ℝ := (lowScalar270 x) * (lowScalar259 x)

noncomputable def lowScalar272 (x : ℝ) : ℝ := (28 / 1 : ℝ)

noncomputable def lowScalar273 (x : ℝ) : ℝ := (lowScalar259 x) * (lowScalar272 x)

noncomputable def lowScalar274 (x : ℝ) : ℝ := (24 / 1 : ℝ)

noncomputable def lowScalar275 (x : ℝ) : ℝ := (lowScalar181 x) * (lowScalar274 x)

noncomputable def lowScalar276 (x : ℝ) : ℝ := (lowScalar275 x) * (lowScalar259 x)

noncomputable def lowScalar277 (x : ℝ) : ℝ := (252 / 1 : ℝ)

noncomputable def lowScalar278 (x : ℝ) : ℝ := (lowScalar259 x) * (lowScalar277 x)

noncomputable def lowScalar279 (x : ℝ) : ℝ := (lowScalar206 x) + (lowScalar268 x)

noncomputable def lowScalar280 (x : ℝ) : ℝ := (lowScalar218 x) + (lowScalar271 x)

noncomputable def lowScalar281 (x : ℝ) : ℝ := (lowScalar238 x) + (lowScalar273 x)

noncomputable def lowScalar282 (x : ℝ) : ℝ := (lowScalar252 x) + (lowScalar276 x)

noncomputable def lowScalar283 (x : ℝ) : ℝ := (lowScalar254 x) + (lowScalar278 x)

noncomputable abbrev qLower (x : ℝ) : ℝ := lowScalar14 x

noncomputable abbrev qUpper (x : ℝ) : ℝ := lowScalar27 x

noncomputable abbrev lambdaScaled (x : ℝ) : ℝ := lowScalar42 x

noncomputable abbrev sigmaScaled (x : ℝ) : ℝ := lowScalar60 x

noncomputable abbrev sigmaFloorScaled (x : ℝ) : ℝ := lowScalar82 x

noncomputable abbrev hScaled (x : ℝ) : ℝ := lowScalar91 x

noncomputable abbrev vScaled (x : ℝ) : ℝ := lowScalar100 x

noncomputable abbrev gScaled (x : ℝ) : ℝ := lowScalar108 x

noncomputable abbrev gapScaled (x : ℝ) : ℝ := lowScalar117 x

noncomputable abbrev exceptionalScaled (x : ℝ) : ℝ := lowScalar150 x

noncomputable abbrev nodeMoment12 (x : ℝ) : ℝ := lowScalar177 x

noncomputable abbrev locationA (x : ℝ) : ℝ := lowScalar279 x

noncomputable abbrev locationB (x : ℝ) : ℝ := lowScalar280 x

noncomputable abbrev locationC (x : ℝ) : ℝ := lowScalar225 x

noncomputable abbrev energyA (x : ℝ) : ℝ := lowScalar281 x

noncomputable abbrev energyB (x : ℝ) : ℝ := lowScalar282 x

noncomputable abbrev energyC (x : ℝ) : ℝ := lowScalar283 x


end BstLean.Part292
