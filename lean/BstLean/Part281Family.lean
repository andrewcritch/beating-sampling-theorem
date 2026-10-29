import BstLean.Part281Rows0
import BstLean.Part281FamilyShard1
import BstLean.Part281FamilyShard2
import BstLean.Part281FamilyShard3
import BstLean.Part281FamilyShard4
import BstLean.Part281FamilyShard5
import BstLean.Part281FamilyShard6
import BstLean.Part281FamilyShard7
import BstLean.Part281FamilyShard8
import BstLean.Part281FamilyShard9
import BstLean.Part281FamilyShard10
import BstLean.Part281FamilyShard11
import BstLean.Part281FamilyShard12
import BstLean.Part281FamilyShard13
import BstLean.Part281FamilyShard14

/-! Frame, row and stated-classifier families for every dimension in M2. -/

namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameFamily (n : ℕ) (hn : n ∈ Icc 11883 12224) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl, hu⟩ := hn
  by_cases h11883 : n = 11883
  · subst n; exact N11883.frameData11883
  by_cases h12224 : n = 12224
  · subst n; exact N12224.frameData12224
  by_cases h1 : n ≤ 11908
  · exact frameShard1 n (by constructor <;> omega)
  by_cases h2 : n ≤ 11933
  · exact frameShard2 n (by constructor <;> omega)
  by_cases h3 : n ≤ 11958
  · exact frameShard3 n (by constructor <;> omega)
  by_cases h4 : n ≤ 11983
  · exact frameShard4 n (by constructor <;> omega)
  by_cases h5 : n ≤ 12008
  · exact frameShard5 n (by constructor <;> omega)
  by_cases h6 : n ≤ 12033
  · exact frameShard6 n (by constructor <;> omega)
  by_cases h7 : n ≤ 12058
  · exact frameShard7 n (by constructor <;> omega)
  by_cases h8 : n ≤ 12083
  · exact frameShard8 n (by constructor <;> omega)
  by_cases h9 : n ≤ 12108
  · exact frameShard9 n (by constructor <;> omega)
  by_cases h10 : n ≤ 12133
  · exact frameShard10 n (by constructor <;> omega)
  by_cases h11 : n ≤ 12158
  · exact frameShard11 n (by constructor <;> omega)
  by_cases h12 : n ≤ 12183
  · exact frameShard12 n (by constructor <;> omega)
  by_cases h13 : n ≤ 12208
  · exact frameShard13 n (by constructor <;> omega)
  exact frameShard14 n (by constructor <;> omega)
noncomputable def rowFamily (n : ℕ) (hn : n ∈ Icc 11883 12224) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl, hu⟩ := hn
  by_cases h11883 : n = 11883
  · subst n; exact row11883
  by_cases h12224 : n = 12224
  · subst n; exact row12224
  by_cases h1 : n ≤ 11908
  · exact rowShard1 n (by constructor <;> omega)
  by_cases h2 : n ≤ 11933
  · exact rowShard2 n (by constructor <;> omega)
  by_cases h3 : n ≤ 11958
  · exact rowShard3 n (by constructor <;> omega)
  by_cases h4 : n ≤ 11983
  · exact rowShard4 n (by constructor <;> omega)
  by_cases h5 : n ≤ 12008
  · exact rowShard5 n (by constructor <;> omega)
  by_cases h6 : n ≤ 12033
  · exact rowShard6 n (by constructor <;> omega)
  by_cases h7 : n ≤ 12058
  · exact rowShard7 n (by constructor <;> omega)
  by_cases h8 : n ≤ 12083
  · exact rowShard8 n (by constructor <;> omega)
  by_cases h9 : n ≤ 12108
  · exact rowShard9 n (by constructor <;> omega)
  by_cases h10 : n ≤ 12133
  · exact rowShard10 n (by constructor <;> omega)
  by_cases h11 : n ≤ 12158
  · exact rowShard11 n (by constructor <;> omega)
  by_cases h12 : n ≤ 12183
  · exact rowShard12 n (by constructor <;> omega)
  by_cases h13 : n ≤ 12208
  · exact rowShard13 n (by constructor <;> omega)
  exact rowShard14 n (by constructor <;> omega)
theorem classifier_stated_11883_12224 (n : ℕ) (hn : n ∈ Icc 11883 12224) (t : ℝ) : 99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl, hu⟩ := hn
  by_cases h11883 : n = 11883
  · subst n; exact classifier_stated_11883 t
  by_cases h12224 : n = 12224
  · subst n; exact classifier_stated_12224 t
  by_cases h1 : n ≤ 11908
  · exact classifierShard1 n (by constructor <;> omega) t
  by_cases h2 : n ≤ 11933
  · exact classifierShard2 n (by constructor <;> omega) t
  by_cases h3 : n ≤ 11958
  · exact classifierShard3 n (by constructor <;> omega) t
  by_cases h4 : n ≤ 11983
  · exact classifierShard4 n (by constructor <;> omega) t
  by_cases h5 : n ≤ 12008
  · exact classifierShard5 n (by constructor <;> omega) t
  by_cases h6 : n ≤ 12033
  · exact classifierShard6 n (by constructor <;> omega) t
  by_cases h7 : n ≤ 12058
  · exact classifierShard7 n (by constructor <;> omega) t
  by_cases h8 : n ≤ 12083
  · exact classifierShard8 n (by constructor <;> omega) t
  by_cases h9 : n ≤ 12108
  · exact classifierShard9 n (by constructor <;> omega) t
  by_cases h10 : n ≤ 12133
  · exact classifierShard10 n (by constructor <;> omega) t
  by_cases h11 : n ≤ 12158
  · exact classifierShard11 n (by constructor <;> omega) t
  by_cases h12 : n ≤ 12183
  · exact classifierShard12 n (by constructor <;> omega) t
  by_cases h13 : n ≤ 12208
  · exact classifierShard13 n (by constructor <;> omega) t
  exact classifierShard14 n (by constructor <;> omega) t
end BstLean.Part281
