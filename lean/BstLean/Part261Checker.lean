import BstLean.Part243Row

/-! Parameterized endpoint checks. The scalar ledger and network packages remain
distinct inputs. All endpoint formulas are the original real formulas. -/
namespace BstLean.Part261
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196

theorem positive_check {h r w f t eT y u e : ℝ}
    (hh : 0 ≤ h) (hr : 0 ≤ r) (hw : 0 < w) (hf : 0 < f) (ht : 0 < t)
    (hT : exp (t*w) ≤ eT)
    (hy : f*((eT-1)/w)*(1+r/(66630010657559783/10^18+h)) ≤ y)
    (hu : exp y ≤ u)
    (he : -t*(1/100) + ((eT-1)/w*(r*(66630010657559784/10^18+h)+r^2) +
      (66630010657559784/10^18+h)^2/f*(u-1)) ≤ -e) :
    Eplus aL h r w f t ≤ -e := by
  have hTb : Tfun w t ≤ (eT-1)/w := by
    unfold Tfun
    exact div_le_div_of_nonneg_right (by linarith) hw.le
  exact (Eplus_le_of_bounds hh hr hw hf ht (by norm_num) x0_lo x0_hi hTb hy hu).trans he

theorem negative_check {h r w f t lo hi y u e : ℝ}
    (hr : 0 ≤ r) (hw : 0 < w) (hf : 0 < f) (ht : t < 0)
    (hg : h+r < 66630010657559783/10^18)
    (hlo : lo ≤ exp (t*w)) (hhi : exp (t*w) ≤ hi) (hi1 : hi ≤ 1)
    (hy : f*((hi-1)/w)*(1-r/(66630010657559783/10^18-h)) ≤ y)
    (hu : exp y ≤ u) (hu1 : u ≤ 1)
    (he : -t*(1/1000) + (-((lo-1)/w)*(r*(66630010657559784/10^18-h)) +
      (66630010657559783/10^18-h)^2/f*(u-1)) ≤ -e) :
    Eminus aL h r w f t ≤ -e := by
  have hTl : (lo-1)/w ≤ Tfun w t := by
    unfold Tfun
    exact div_le_div_of_nonneg_right (by linarith) hw.le
  have hTh : Tfun w t ≤ (hi-1)/w := by
    unfold Tfun
    exact div_le_div_of_nonneg_right (by linarith) hw.le
  exact (Eminus_le_of_bounds hr hw hf ht hg x0_lo x0_hi hTl hTh
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le) hy hu hu1).trans he

/-- The checker retains the complete scalar certificate, including both stored
tail proposals. It proves the actual sampling payment at the chosen tolerance. -/
noncomputable def master {n : ℕ} {w : WorldParameters} {a : AgentParameters}
    (C : ScalarCertificate n w a) (ds tp tm ep em : ℝ)
    (hds : 0 < ds) (htp : 0 < tp) (htm : tm < 0)
    (hep : 0 ≤ ep) (hem : 0 ≤ em)
    (hp : Eplus aL (a.root+ds) C.worldRadius w.frame a.frame tp ≤ -ep)
    (hm : Eminus aL (a.root+ds) C.worldRadius w.frame a.frame tm ≤ -em)
    (hpt : exp (-((n:ℝ)*ep)) ≤ C.upperTail)
    (hmt : exp (-((n:ℝ)*em)) ≤ C.lowerTail)
    (hs : 2*exp (-100) ≤ C.samplingCharge)
    (hactual : 2*exp (-((10^12:ℕ):ℝ)*ds^2) ≤ C.samplingCharge)
    (hr : a.root+ds+C.worldRadius < √(1/100/aL))
    (hroot : 2*(a.root+ds) ≤ √(1/100/aL)) : MasterCertificate n w a where
  toEndpointCertificate := {
    toScalarCertificate := C
    sampleRoot := ds
    positiveTilt := tp
    negativeTilt := tm
    positiveExponent := ep
    negativeExponent := em
    sampleRoot_pos := hds
    positiveTilt_pos := htp
    negativeTilt_neg := htm
    positiveExponent_nonneg := hep
    negativeExponent_nonneg := hem
    positive_enclosure := hp
    negative_enclosure := hm
    positive_tail := hpt
    negative_tail := hmt
    sampling_payment := hs }
  lower_radius := hr
  lower_root := hroot
  actual_sampling := hactual

theorem master_preserves_scalar {n : ℕ} {w : WorldParameters} {a : AgentParameters}
    (C : ScalarCertificate n w a) (ds tp tm ep em : ℝ)
    (hds) (htp) (htm) (hep) (hem) (hp) (hm) (hpt) (hmt) (hs) (hactual) (hr) (hroot) :
    (master C ds tp tm ep em hds htp htm hep hem hp hm hpt hmt hs hactual hr hroot).toScalarCertificate = C := rfl

end BstLean.Part261
