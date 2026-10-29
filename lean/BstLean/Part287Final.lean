import BstLean.Part287Bands

/-! The stated classifier on the complete Part287 interval, for both parities. -/
namespace BstLean.Part287
open BstLean.Part130 BstLean.Part157

theorem classifier_stated_13484_16199 : ∀ n ∈ Set.Icc (13484 : ℕ) 16199, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := interval13484_16199.classifier

theorem classifier_stated_13225_16199 : ∀ n ∈ Set.Icc (13225 : ℕ) 16199, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := uniformBandInputs.classifier

end BstLean.Part287
