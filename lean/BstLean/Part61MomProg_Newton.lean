import BstLean.Part61Defs
import BstLean.Part56MomProg_Toolkit

namespace BstLean.Part61.MomProgAux

open BstLean.Cost BstLean.Part56.MomProg

/-- The node uses three arithmetic instructions per Newton step. -/
theorem hp_newton (N : ℕ) :
    HasProg (fun (w : Unit → ℝ) (_ : Unit) => newt61 N (w ())) (4 * N) := by
  induction N with
  | zero =>
    exact hp_congr (hp_args (fun _ : Unit => Arg.cst 1) (fun _ => rfl))
      (fun _ _ => by simp [Arg.eval, newt61])
  | succ N ih =>
    have hd := hp_op (ι := Unit ⊕ Unit) .div
      (.inp (.inl ())) (.inp (.inr ())) rfl rfl
    have ha := hp_op (ι := (Unit ⊕ Unit) ⊕ Unit) .add
      (.inp (.inl (.inr ()))) (.inp (.inr ())) rfl rfl
    have ht := hp_op (ι := ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) .add
      (.cst 1) (.cst 1) rfl rfl
    have hh := hp_op (ι := (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) .div
      (.inp (.inl (.inr ()))) (.inp (.inr ())) rfl rfl
    have h := hp_bind ih (hp_bind hd (hp_bind ha (hp_bind ht hh)))
    refine hp_mono (hp_congr h ?_) (by omega)
    intro w u
    norm_num [Op.eval, Arg.eval, newt61]

end BstLean.Part61.MomProgAux
