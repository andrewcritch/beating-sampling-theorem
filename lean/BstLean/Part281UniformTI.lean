import BstLean.Part281NormalizedE0
import BstLean.Part281NormalizedE1
import BstLean.Part281NormalizedE2
import BstLean.Part281NormalizedE3
import BstLean.Part281NormalizedO
import BstLean.Part281SClasses
import BstLean.Part263Events
namespace BstLean.Part281.TI
open BstLean.Part264b
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part246 BstLean.Part255

theorem uniformO {n : ℕ} (hn : 11883 ≤ n) :
    o3_kO n 46 ((mA n : ℝ)*(1/2+√23/n)) ((mA n : ℝ)*(1/2+√23/n)) ≤
      n * ((17139/500000)) := by
  rw [norm_o (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedO (invN_bounds hn)) (by positivity)

theorem uniform_am_positive {n : ℕ} (hn : 11883 ≤ n) : 0 < s3am n 46 :=
  (uniformS0 hn (c := (69/200 : ℝ)) (by constructor <;> norm_num)).1
theorem uniformE10W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (398969473/1000000000) (685010303/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (685010303/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (312477/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE10W (invN_bounds hn) hc) (by positivity)

theorem uniformNum10W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨0,by decide⟩).wlo (parameters ⟨0,by decide⟩).whi
      (parameters ⟨0,by decide⟩).wE (parameters ⟨0,by decide⟩).o
      (parameters ⟨0,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass10W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE10W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE10C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (231978551/500000000) (37365067/62500000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (37365067/62500000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (115033/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE10C (invN_bounds hn) hc) (by positivity)

theorem uniformNum10C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨0,by decide⟩).clo (parameters ⟨0,by decide⟩).chi
      (parameters ⟨0,by decide⟩).cE (parameters ⟨0,by decide⟩).o
      (parameters ⟨0,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass10C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE10C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE11W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (7954879/20000000) (341940353/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (341940353/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (124851/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE11W (invN_bounds hn) hc) (by positivity)

theorem uniformNum11W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨1,by decide⟩).wlo (parameters ⟨1,by decide⟩).whi
      (parameters ⟨1,by decide⟩).wE (parameters ⟨1,by decide⟩).o
      (parameters ⟨1,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass11W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE11W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE11C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (462745419/1000000000) (596662023/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (596662023/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (287271/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE11C (invN_bounds hn) hc) (by positivity)

theorem uniformNum11C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨1,by decide⟩).clo (parameters ⟨1,by decide⟩).chi
      (parameters ⟨1,by decide⟩).cE (parameters ⟨1,by decide⟩).o
      (parameters ⟨1,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass11C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE11C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE12W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (396519081/1000000000) (341375127/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (341375127/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (311779/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE12W (invN_bounds hn) hc) (by positivity)

theorem uniformNum12W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨2,by decide⟩).wlo (parameters ⟨2,by decide⟩).whi
      (parameters ⟨2,by decide⟩).wE (parameters ⟨2,by decide⟩).o
      (parameters ⟨2,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass12W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE12W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE12C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (230767047/500000000) (74435321/125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (74435321/125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (3587/6250) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE12C (invN_bounds hn) hc) (by positivity)

theorem uniformNum12C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨2,by decide⟩).clo (parameters ⟨2,by decide⟩).chi
      (parameters ⟨2,by decide⟩).cE (parameters ⟨2,by decide⟩).o
      (parameters ⟨2,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass12C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE12C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE13W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (24705929/62500000) (170404737/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (170404737/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (622861/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE13W (invN_bounds hn) hc) (by positivity)

theorem uniformNum13W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨3,by decide⟩).wlo (parameters ⟨3,by decide⟩).whi
      (parameters ⟨3,by decide⟩).wE (parameters ⟨3,by decide⟩).o
      (parameters ⟨3,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass13W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE13W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE13C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (460323127/1000000000) (118860541/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (118860541/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (573299/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE13C (invN_bounds hn) hc) (by positivity)

theorem uniformNum13C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨3,by decide⟩).clo (parameters ⟨3,by decide⟩).chi
      (parameters ⟨3,by decide⟩).cE (parameters ⟨3,by decide⟩).o
      (parameters ⟨3,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass13C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE13C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE14W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (197035649/500000000) (680486789/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (680486789/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (311083/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE14W (invN_bounds hn) hc) (by positivity)

theorem uniformNum14W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨4,by decide⟩).wlo (parameters ⟨4,by decide⟩).whi
      (parameters ⟨4,by decide⟩).wE (parameters ⟨4,by decide⟩).o
      (parameters ⟨4,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass14W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE14W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE14C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (229556259/500000000) (148280609/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (148280609/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (572679/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE14C (invN_bounds hn) hc) (by positivity)

theorem uniformNum14C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨4,by decide⟩).clo (parameters ⟨4,by decide⟩).chi
      (parameters ⟨4,by decide⟩).cE (parameters ⟨4,by decide⟩).o
      (parameters ⟨4,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass14C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE14C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE15W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (196424191/500000000) (679353779/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (679353779/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (621471/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE15W (invN_bounds hn) hc) (by positivity)

theorem uniformNum15W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨5,by decide⟩).wlo (parameters ⟨5,by decide⟩).whi
      (parameters ⟨5,by decide⟩).wE (parameters ⟨5,by decide⟩).o
      (parameters ⟨5,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass15W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE15W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE15C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (91580453/200000000) (591941761/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (591941761/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (28603/50000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE15C (invN_bounds hn) hc) (by positivity)

theorem uniformNum15C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨5,by decide⟩).clo (parameters ⟨5,by decide⟩).chi
      (parameters ⟨5,by decide⟩).cE (parameters ⟨5,by decide⟩).o
      (parameters ⟨5,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass15C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE15C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE16W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (195813057/500000000) (339109959/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (339109959/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (310389/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE16W (invN_bounds hn) hc) (by positivity)

theorem uniformNum16W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨6,by decide⟩).wlo (parameters ⟨6,by decide⟩).whi
      (parameters ⟨6,by decide⟩).wE (parameters ⟨6,by decide⟩).o
      (parameters ⟨6,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass16W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE16W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE16C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (28543273/62500000) (590760681/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (590760681/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (285721/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE16C (invN_bounds hn) hc) (by positivity)

theorem uniformNum16C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨6,by decide⟩).clo (parameters ⟨6,by decide⟩).chi
      (parameters ⟨6,by decide⟩).cE (parameters ⟨6,by decide⟩).o
      (parameters ⟨6,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass16C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE16C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE17W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (390404493/1000000000) (84635651/125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (84635651/125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (310043/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE17W (invN_bounds hn) hc) (by positivity)

theorem uniformNum17W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨7,by decide⟩).wlo (parameters ⟨7,by decide⟩).whi
      (parameters ⟨7,by decide⟩).wE (parameters ⟨7,by decide⟩).o
      (parameters ⟨7,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass17W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE17W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE17C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (227741413/500000000) (589579197/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (589579197/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (22833/40000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE17C (invN_bounds hn) hc) (by positivity)

theorem uniformNum17C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨7,by decide⟩).clo (parameters ⟨7,by decide⟩).chi
      (parameters ⟨7,by decide⟩).cE (parameters ⟨7,by decide⟩).o
      (parameters ⟨7,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass17C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE17C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE18W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (194591759/500000000) (13518993/20000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (13518993/20000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (309697/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE18W (invN_bounds hn) hc) (by positivity)

theorem uniformNum18W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨8,by decide⟩).wlo (parameters ⟨8,by decide⟩).whi
      (parameters ⟨8,by decide⟩).wE (parameters ⟨8,by decide⟩).o
      (parameters ⟨8,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass18W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE18W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE18C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (227136819/500000000) (147099327/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (147099327/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (570209/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE18C (invN_bounds hn) hc) (by positivity)

theorem uniformNum18C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨8,by decide⟩).clo (parameters ⟨8,by decide⟩).chi
      (parameters ⟨8,by decide⟩).cE (parameters ⟨8,by decide⟩).o
      (parameters ⟨8,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass18C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE18C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE19W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (193981593/500000000) (134962649/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (134962649/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (38669/62500) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE19W (invN_bounds hn) hc) (by positivity)

theorem uniformNum19W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨9,by decide⟩).wlo (parameters ⟨9,by decide⟩).whi
      (parameters ⟨9,by decide⟩).wE (parameters ⟨9,by decide⟩).o
      (parameters ⟨9,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass19W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE19W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE19C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (90612961/200000000) (117443003/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (117443003/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (569593/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE19C (invN_bounds hn) hc) (by positivity)

theorem uniformNum19C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨9,by decide⟩).clo (parameters ⟨9,by decide⟩).chi
      (parameters ⟨9,by decide⟩).cE (parameters ⟨9,by decide⟩).o
      (parameters ⟨9,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass19C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE19C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE20W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (386743497/1000000000) (673675993/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (673675993/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (123603/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE20W (invN_bounds hn) hc) (by positivity)

theorem uniformNum20W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨10,by decide⟩).wlo (parameters ⟨10,by decide⟩).whi
      (parameters ⟨10,by decide⟩).wE (parameters ⟨10,by decide⟩).o
      (parameters ⟨10,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass20W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE20W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE20C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (18074253/40000000) (1831351/3125000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (1831351/3125000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (568979/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE20C (invN_bounds hn) hc) (by positivity)

theorem uniformNum20C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨10,by decide⟩).clo (parameters ⟨10,by decide⟩).chi
      (parameters ⟨10,by decide⟩).cE (parameters ⟨10,by decide⟩).o
      (parameters ⟨10,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass20C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE20C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE21W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (7710489/20000000) (672537897/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (672537897/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (617327/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE21W (invN_bounds hn) hc) (by positivity)

theorem uniformNum21W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨11,by decide⟩).wlo (parameters ⟨11,by decide⟩).whi
      (parameters ⟨11,by decide⟩).wE (parameters ⟨11,by decide⟩).o
      (parameters ⟨11,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass21W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE21W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE21C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (225324099/500000000) (292424611/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (292424611/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (284183/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE21C (invN_bounds hn) hc) (by positivity)

theorem uniformNum21C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨11,by decide⟩).clo (parameters ⟨11,by decide⟩).chi
      (parameters ⟨11,by decide⟩).cE (parameters ⟨11,by decide⟩).o
      (parameters ⟨11,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass21C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE21C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE22W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (192153021/500000000) (671398957/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (671398957/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (616639/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE22W (invN_bounds hn) hc) (by positivity)

theorem uniformNum22W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨12,by decide⟩).wlo (parameters ⟨12,by decide⟩).whi
      (parameters ⟨12,by decide⟩).wE (parameters ⟨12,by decide⟩).o
      (parameters ⟨12,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass22W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE22W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE22C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (449440423/1000000000) (291832861/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (291832861/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (567753/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE22C (invN_bounds hn) hc) (by positivity)

theorem uniformNum22C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨12,by decide⟩).clo (parameters ⟨12,by decide⟩).chi
      (parameters ⟨12,by decide⟩).cE (parameters ⟨12,by decide⟩).o
      (parameters ⟨12,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass22C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE22C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE23W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (383088273/1000000000) (335129587/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (335129587/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (615953/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE23W (invN_bounds hn) hc) (by positivity)

theorem uniformNum23W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨13,by decide⟩).wlo (parameters ⟨13,by decide⟩).whi
      (parameters ⟨13,by decide⟩).wE (parameters ⟨13,by decide⟩).o
      (parameters ⟨13,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass23W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE23W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE23C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (448232999/1000000000) (29124091/50000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (29124091/50000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (283571/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE23C (invN_bounds hn) hc) (by positivity)

theorem uniformNum23C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨13,by decide⟩).clo (parameters ⟨13,by decide⟩).chi
      (parameters ⟨13,by decide⟩).cE (parameters ⟨13,by decide⟩).o
      (parameters ⟨13,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass23C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE23C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE24W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (190935571/500000000) (167279637/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (167279637/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (153817/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE24W (invN_bounds hn) hc) (by positivity)

theorem uniformNum24W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨14,by decide⟩).wlo (parameters ⟨14,by decide⟩).whi
      (parameters ⟨14,by decide⟩).wE (parameters ⟨14,by decide⟩).o
      (parameters ⟨14,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass24W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE24W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE24C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (447025927/1000000000) (290648759/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (290648759/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (566531/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE24C (invN_bounds hn) hc) (by positivity)

theorem uniformNum24C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨14,by decide⟩).clo (parameters ⟨14,by decide⟩).chi
      (parameters ⟨14,by decide⟩).cE (parameters ⟨14,by decide⟩).o
      (parameters ⟨14,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass24C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE24C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE25W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (380654647/1000000000) (333988541/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (333988541/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (76823/125000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE25W (invN_bounds hn) hc) (by positivity)

theorem uniformNum25W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨15,by decide⟩).wlo (parameters ⟨15,by decide⟩).whi
      (parameters ⟨15,by decide⟩).wE (parameters ⟨15,by decide⟩).o
      (parameters ⟨15,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass25W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE25W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE25C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (111454801/250000000) (116022563/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (116022563/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (565921/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE25C (invN_bounds hn) hc) (by positivity)

theorem uniformNum25C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨15,by decide⟩).clo (parameters ⟨15,by decide⟩).chi
      (parameters ⟨15,by decide⟩).cE (parameters ⟨15,by decide⟩).o
      (parameters ⟨15,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass25C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE25C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE26W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (379438787/1000000000) (666834777/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (666834777/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (613901/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE26W (invN_bounds hn) hc) (by positivity)

theorem uniformNum26W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨16,by decide⟩).wlo (parameters ⟨16,by decide⟩).whi
      (parameters ⟨16,by decide⟩).wE (parameters ⟨16,by decide⟩).o
      (parameters ⟨16,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass26W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE26W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE26C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (13894151/31250000) (578927713/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (578927713/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (8833/15625) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE26C (invN_bounds hn) hc) (by positivity)

theorem uniformNum26C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨16,by decide⟩).clo (parameters ⟨16,by decide⟩).chi
      (parameters ⟨16,by decide⟩).cE (parameters ⟨16,by decide⟩).o
      (parameters ⟨16,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass26C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE26C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE27W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (9455589/25000000) (41605727/62500000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (41605727/62500000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (613219/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE27W (invN_bounds hn) hc) (by positivity)

theorem uniformNum27W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨17,by decide⟩).wlo (parameters ⟨17,by decide⟩).whi
      (parameters ⟨17,by decide⟩).wE (parameters ⟨17,by decide⟩).o
      (parameters ⟨17,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass27W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE27W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE27C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (55425851/125000000) (577742211/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (577742211/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (112941/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE27C (invN_bounds hn) hc) (by positivity)

theorem uniformNum27C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨17,by decide⟩).clo (parameters ⟨17,by decide⟩).chi
      (parameters ⟨17,by decide⟩).cE (parameters ⟨17,by decide⟩).o
      (parameters ⟨17,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass27C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE27C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE28W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (75401793/200000000) (664547649/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (664547649/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (306269/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE28W (invN_bounds hn) hc) (by positivity)

theorem uniformNum28W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨18,by decide⟩).wlo (parameters ⟨18,by decide⟩).whi
      (parameters ⟨18,by decide⟩).wE (parameters ⟨18,by decide⟩).o
      (parameters ⟨18,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass28W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE28W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE28C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (442201133/1000000000) (57655631/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (57655631/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (282049/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE28C (invN_bounds hn) hc) (by positivity)

theorem uniformNum28C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨18,by decide⟩).clo (parameters ⟨18,by decide⟩).chi
      (parameters ⟨18,by decide⟩).cE (parameters ⟨18,by decide⟩).o
      (parameters ⟨18,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass28C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE28C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE29W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (187897501/500000000) (66340283/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (66340283/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (611857/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE29W (invN_bounds hn) hc) (by positivity)

theorem uniformNum29W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨19,by decide⟩).wlo (parameters ⟨19,by decide⟩).whi
      (parameters ⟨19,by decide⟩).wE (parameters ⟨19,by decide⟩).o
      (parameters ⟨19,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass29W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE29W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE29C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (220497903/500000000) (575370011/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (575370011/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (140873/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE29C (invN_bounds hn) hc) (by positivity)

theorem uniformNum29C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨19,by decide⟩).clo (parameters ⟨19,by decide⟩).chi
      (parameters ⟨19,by decide⟩).cE (parameters ⟨19,by decide⟩).o
      (parameters ⟨19,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass29C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE29C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE30W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (93645417/250000000) (26490287/40000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (26490287/40000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (305589/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE30W (invN_bounds hn) hc) (by positivity)

theorem uniformNum30W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨20,by decide⟩).wlo (parameters ⟨20,by decide⟩).whi
      (parameters ⟨20,by decide⟩).wE (parameters ⟨20,by decide⟩).o
      (parameters ⟨20,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass30W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE30W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE30C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (219895413/500000000) (287091657/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (287091657/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (281443/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE30C (invN_bounds hn) hc) (by positivity)

theorem uniformNum30C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨20,by decide⟩).clo (parameters ⟨20,by decide⟩).chi
      (parameters ⟨20,by decide⟩).cE (parameters ⟨20,by decide⟩).o
      (parameters ⟨20,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass30C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE30C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE31W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (186684481/500000000) (132222137/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (132222137/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (1221/2000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE31W (invN_bounds hn) hc) (by positivity)

theorem uniformNum31W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨21,by decide⟩).wlo (parameters ⟨21,by decide⟩).whi
      (parameters ⟨21,by decide⟩).wE (parameters ⟨21,by decide⟩).o
      (parameters ⟨21,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass31W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE31W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE31C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (438586193/1000000000) (572996219/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (572996219/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (281141/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE31C (invN_bounds hn) hc) (by positivity)

theorem uniformNum31C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨21,by decide⟩).clo (parameters ⟨21,by decide⟩).chi
      (parameters ⟨21,by decide⟩).cE (parameters ⟨21,by decide⟩).o
      (parameters ⟨21,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass31C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE31C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE32W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (93039221/250000000) (659963361/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (659963361/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (609823/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE32W (invN_bounds hn) hc) (by positivity)

theorem uniformNum32W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨22,by decide⟩).wlo (parameters ⟨22,by decide⟩).whi
      (parameters ⟨22,by decide⟩).wE (parameters ⟨22,by decide⟩).o
      (parameters ⟨22,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass32W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE32W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE32C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (218690953/500000000) (71476091/125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (71476091/125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (561679/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE32C (invN_bounds hn) hc) (by positivity)

theorem uniformNum32C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨22,by decide⟩).clo (parameters ⟨22,by decide⟩).chi
      (parameters ⟨22,by decide⟩).cE (parameters ⟨22,by decide⟩).o
      (parameters ⟨22,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass32C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE32C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE33W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (46368179/125000000) (164703801/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (164703801/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (609147/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE33W (invN_bounds hn) hc) (by positivity)

theorem uniformNum33W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨23,by decide⟩).wlo (parameters ⟨23,by decide⟩).whi
      (parameters ⟨23,by decide⟩).wE (parameters ⟨23,by decide⟩).o
      (parameters ⟨23,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass33W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE33W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE33C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (87235593/200000000) (570620841/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (570620841/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (140269/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE33C (invN_bounds hn) hc) (by positivity)

theorem uniformNum33C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨23,by decide⟩).clo (parameters ⟨23,by decide⟩).chi
      (parameters ⟨23,by decide⟩).cE (parameters ⟨23,by decide⟩).o
      (parameters ⟨23,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass33C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE33C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE34W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (73946921/200000000) (131533243/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (131533243/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (76059/125000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE34W (invN_bounds hn) hc) (by positivity)

theorem uniformNum34W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨24,by decide⟩).wlo (parameters ⟨24,by decide⟩).whi
      (parameters ⟨24,by decide⟩).wE (parameters ⟨24,by decide⟩).o
      (parameters ⟨24,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass34W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE34W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE34C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (434974369/1000000000) (569432557/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (569432557/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (22419/40000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE34C (invN_bounds hn) hc) (by positivity)

theorem uniformNum34C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨24,by decide⟩).clo (parameters ⟨24,by decide⟩).chi
      (parameters ⟨24,by decide⟩).cE (parameters ⟨24,by decide⟩).o
      (parameters ⟨24,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass34C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE34C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE35W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (368524401/1000000000) (131303279/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (131303279/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (607797/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE35W (invN_bounds hn) hc) (by positivity)

theorem uniformNum35W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨25,by decide⟩).wlo (parameters ⟨25,by decide⟩).whi
      (parameters ⟨25,by decide⟩).wE (parameters ⟨25,by decide⟩).o
      (parameters ⟨25,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass35W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE35W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE35C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (433771117/1000000000) (284121939/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (284121939/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (279937/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE35C (invN_bounds hn) hc) (by positivity)

theorem uniformNum35C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨25,by decide⟩).clo (parameters ⟨25,by decide⟩).chi
      (parameters ⟨25,by decide⟩).cE (parameters ⟨25,by decide⟩).o
      (parameters ⟨25,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass35C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE35C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE36W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (367314819/1000000000) (131073149/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (131073149/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (151781/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE36W (invN_bounds hn) hc) (by positivity)

theorem uniformNum36W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨26,by decide⟩).wlo (parameters ⟨26,by decide⟩).whi
      (parameters ⟨26,by decide⟩).wE (parameters ⟨26,by decide⟩).o
      (parameters ⟨26,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass36W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE36W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE36C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (432568209/1000000000) (113410961/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (113410961/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (279637/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE36C (invN_bounds hn) hc) (by positivity)

theorem uniformNum36C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨26,by decide⟩).clo (parameters ⟨26,by decide⟩).chi
      (parameters ⟨26,by decide⟩).cE (parameters ⟨26,by decide⟩).o
      (parameters ⟨26,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass36C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE36C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE37W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (366105859/1000000000) (327107133/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (327107133/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (151613/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE37W (invN_bounds hn) hc) (by positivity)

theorem uniformNum37W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨27,by decide⟩).wlo (parameters ⟨27,by decide⟩).whi
      (parameters ⟨27,by decide⟩).wE (parameters ⟨27,by decide⟩).o
      (parameters ⟨27,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass37W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE37W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE37C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (107841411/250000000) (70733167/125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (70733167/125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (139669/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE37C (invN_bounds hn) hc) (by positivity)

theorem uniformNum37C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨27,by decide⟩).clo (parameters ⟨27,by decide⟩).chi
      (parameters ⟨27,by decide⟩).cE (parameters ⟨27,by decide⟩).o
      (parameters ⟨27,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass37C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE37C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE38W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (182448759/500000000) (653061959/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (653061959/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (30289/50000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE38W (invN_bounds hn) hc) (by positivity)

theorem uniformNum38W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨28,by decide⟩).wlo (parameters ⟨28,by decide⟩).whi
      (parameters ⟨28,by decide⟩).wE (parameters ⟨28,by decide⟩).o
      (parameters ⟨28,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass38W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE38W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE38C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (215081711/500000000) (282337737/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (282337737/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (558077/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE38C (invN_bounds hn) hc) (by positivity)

theorem uniformNum38C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨28,by decide⟩).clo (parameters ⟨28,by decide⟩).chi
      (parameters ⟨28,by decide⟩).cE (parameters ⟨28,by decide⟩).o
      (parameters ⟨28,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass38C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE38C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE39W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (90922449/250000000) (81488603/125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (81488603/125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (60511/100000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE39W (invN_bounds hn) hc) (by positivity)

theorem uniformNum39W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨29,by decide⟩).wlo (parameters ⟨29,by decide⟩).whi
      (parameters ⟨29,by decide⟩).wE (parameters ⟨29,by decide⟩).o
      (parameters ⟨29,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass39W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE39W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE39C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (428961543/1000000000) (563485219/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (563485219/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (13937/25000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE39C (invN_bounds hn) hc) (by positivity)

theorem uniformNum39C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨29,by decide⟩).clo (parameters ⟨29,by decide⟩).chi
      (parameters ⟨29,by decide⟩).cE (parameters ⟨29,by decide⟩).o
      (parameters ⟨29,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass39C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE39C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE40W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (90620673/250000000) (650754863/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (650754863/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (15111/25000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE40W (invN_bounds hn) hc) (by positivity)

theorem uniformNum40W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨30,by decide⟩).wlo (parameters ⟨30,by decide⟩).whi
      (parameters ⟨30,by decide⟩).wE (parameters ⟨30,by decide⟩).o
      (parameters ⟨30,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass40W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE40W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE40C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (85552001/200000000) (56229457/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (56229457/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (139221/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE40C (invN_bounds hn) hc) (by positivity)

theorem uniformNum40C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨30,by decide⟩).clo (parameters ⟨30,by decide⟩).chi
      (parameters ⟨30,by decide⟩).cE (parameters ⟨30,by decide⟩).o
      (parameters ⟨30,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass40C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE40C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE41W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (90319051/250000000) (162400019/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (162400019/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (150943/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE41W (invN_bounds hn) hc) (by positivity)

theorem uniformNum41W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨31,by decide⟩).wlo (parameters ⟨31,by decide⟩).whi
      (parameters ⟨31,by decide⟩).wE (parameters ⟨31,by decide⟩).o
      (parameters ⟨31,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass41W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE41W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE41C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (53319851/125000000) (561103529/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (561103529/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (556289/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE41C (invN_bounds hn) hc) (by positivity)

theorem uniformNum41C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨31,by decide⟩).clo (parameters ⟨31,by decide⟩).chi
      (parameters ⟨31,by decide⟩).cE (parameters ⟨31,by decide⟩).o
      (parameters ⟨31,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass41C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE41C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE42W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (90017583/250000000) (129688893/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (129688893/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (18847/31250) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE42W (invN_bounds hn) hc) (by positivity)

theorem uniformNum42W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨32,by decide⟩).wlo (parameters ⟨32,by decide⟩).whi
      (parameters ⟨32,by decide⟩).wE (parameters ⟨32,by decide⟩).o
      (parameters ⟨32,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass42W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE42W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE42C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (3323109/7812500) (111982419/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (111982419/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (277847/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE42C (invN_bounds hn) hc) (by positivity)

theorem uniformNum42C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨32,by decide⟩).clo (parameters ⟨32,by decide⟩).chi
      (parameters ⟨32,by decide⟩).cE (parameters ⟨32,by decide⟩).o
      (parameters ⟨32,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass42C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE42C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE43W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (358865073/1000000000) (64728803/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (64728803/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (301219/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE43W (invN_bounds hn) hc) (by positivity)

theorem uniformNum43W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨33,by decide⟩).wlo (parameters ⟨33,by decide⟩).whi
      (parameters ⟨33,by decide⟩).wE (parameters ⟨33,by decide⟩).o
      (parameters ⟨33,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass43W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE43W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE43C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (106039359/250000000) (558720271/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (558720271/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (5551/10000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE43C (invN_bounds hn) hc) (by positivity)

theorem uniformNum43C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨33,by decide⟩).clo (parameters ⟨33,by decide⟩).chi
      (parameters ⟨33,by decide⟩).cE (parameters ⟨33,by decide⟩).o
      (parameters ⟨33,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass43C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE43C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE44W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (89415107/250000000) (161532693/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (161532693/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (150443/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE44W (invN_bounds hn) hc) (by positivity)

theorem uniformNum44W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨34,by decide⟩).wlo (parameters ⟨34,by decide⟩).whi
      (parameters ⟨34,by decide⟩).wE (parameters ⟨34,by decide⟩).o
      (parameters ⟨34,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass44W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE44W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE44C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (422957259/1000000000) (278764027/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (278764027/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (138627/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE44C (invN_bounds hn) hc) (by positivity)

theorem uniformNum44C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨34,by decide⟩).clo (parameters ⟨34,by decide⟩).chi
      (parameters ⟨34,by decide⟩).cE (parameters ⟨34,by decide⟩).o
      (parameters ⟨34,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass44C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE44C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE45W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (178228197/500000000) (161243173/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (161243173/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (601107/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE45W (invN_bounds hn) hc) (by positivity)

theorem uniformNum45W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨35,by decide⟩).wlo (parameters ⟨35,by decide⟩).whi
      (parameters ⟨35,by decide⟩).wE (parameters ⟨35,by decide⟩).o
      (parameters ⟨35,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass45W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE45W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE45C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (421757421/1000000000) (69541931/125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (69541931/125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (138479/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE45C (invN_bounds hn) hc) (by positivity)

theorem uniformNum45C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨35,by decide⟩).clo (parameters ⟨35,by decide⟩).chi
      (parameters ⟨35,by decide⟩).cE (parameters ⟨35,by decide⟩).o
      (parameters ⟨35,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass45C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE45C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE46W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (355252971/1000000000) (643813791/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (643813791/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (150111/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE46W (invN_bounds hn) hc) (by positivity)

theorem uniformNum46W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨36,by decide⟩).wlo (parameters ⟨36,by decide⟩).whi
      (parameters ⟨36,by decide⟩).wE (parameters ⟨36,by decide⟩).o
      (parameters ⟨36,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass46W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE46W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE46C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (210278961/500000000) (11102849/20000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (11102849/20000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (22133/40000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE46C (invN_bounds hn) hc) (by positivity)

theorem uniformNum46C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨36,by decide⟩).clo (parameters ⟨36,by decide⟩).chi
      (parameters ⟨36,by decide⟩).cE (parameters ⟨36,by decide⟩).o
      (parameters ⟨36,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass46C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE46C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE47W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (177025079/500000000) (64265407/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (64265407/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (599781/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE47W (invN_bounds hn) hc) (by positivity)

theorem uniformNum47W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨37,by decide⟩).wlo (parameters ⟨37,by decide⟩).whi
      (parameters ⟨37,by decide⟩).wE (parameters ⟨37,by decide⟩).o
      (parameters ⟨37,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass47W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE47W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE47C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (419358761/1000000000) (553949063/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (553949063/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (276367/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE47C (invN_bounds hn) hc) (by positivity)

theorem uniformNum47C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨37,by decide⟩).clo (parameters ⟨37,by decide⟩).chi
      (parameters ⟨37,by decide⟩).cE (parameters ⟨37,by decide⟩).o
      (parameters ⟨37,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass47C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE47C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE48W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (352847953/1000000000) (641493529/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (641493529/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (599119/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE48W (invN_bounds hn) hc) (by positivity)

theorem uniformNum48W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨38,by decide⟩).wlo (parameters ⟨38,by decide⟩).whi
      (parameters ⟨38,by decide⟩).wE (parameters ⟨38,by decide⟩).o
      (parameters ⟨38,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass48W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE48W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE48C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (418159937/1000000000) (552755287/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (552755287/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (110429/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE48C (invN_bounds hn) hc) (by positivity)

theorem uniformNum48C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨38,by decide⟩).clo (parameters ⟨38,by decide⟩).chi
      (parameters ⟨38,by decide⟩).cE (parameters ⟨38,by decide⟩).o
      (parameters ⟨38,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass48C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE48C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE49W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (70329271/200000000) (64033217/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (64033217/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (299229/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE49W (invN_bounds hn) hc) (by positivity)

theorem uniformNum49W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨39,by decide⟩).wlo (parameters ⟨39,by decide⟩).whi
      (parameters ⟨39,by decide⟩).wE (parameters ⟨39,by decide⟩).o
      (parameters ⟨39,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass49W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE49W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE49C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (8339229/20000000) (551561121/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (551561121/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (137889/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE49C (invN_bounds hn) hc) (by positivity)

theorem uniformNum49C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨39,by decide⟩).clo (parameters ⟨39,by decide⟩).chi
      (parameters ⟨39,by decide⟩).cE (parameters ⟨39,by decide⟩).o
      (parameters ⟨39,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass49C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE49C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE50W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (87611341/250000000) (639169993/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (639169993/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (597797/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE50W (invN_bounds hn) hc) (by positivity)

theorem uniformNum50W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨40,by decide⟩).wlo (parameters ⟨40,by decide⟩).whi
      (parameters ⟨40,by decide⟩).wE (parameters ⟨40,by decide⟩).o
      (parameters ⟨40,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass50W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE50W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE50C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (4157633/10000000) (550366567/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (550366567/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (550969/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE50C (invN_bounds hn) hc) (by positivity)

theorem uniformNum50C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨40,by decide⟩).clo (parameters ⟨40,by decide⟩).chi
      (parameters ⟨40,by decide⟩).cE (parameters ⟨40,by decide⟩).o
      (parameters ⟨40,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass50C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE50C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE51W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (349244977/1000000000) (638006999/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (638006999/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (298569/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE51W (invN_bounds hn) hc) (by positivity)

theorem uniformNum51W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨41,by decide⟩).wlo (parameters ⟨41,by decide⟩).whi
      (parameters ⟨41,by decide⟩).wE (parameters ⟨41,by decide⟩).o
      (parameters ⟨41,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass51W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE51W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE51C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (207282743/500000000) (4393373/8000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (4393373/8000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (275191/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE51C (invN_bounds hn) hc) (by positivity)

theorem uniformNum51C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨41,by decide⟩).clo (parameters ⟨41,by decide⟩).chi
      (parameters ⟨41,by decide⟩).cE (parameters ⟨41,by decide⟩).o
      (parameters ⟨41,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass51C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE51C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE52W {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (69609039/200000000) (636843189/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (636843189/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (1864/3125) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE52W (invN_bounds hn) hc) (by positivity)

theorem uniformNum52W {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨42,by decide⟩).wlo (parameters ⟨42,by decide⟩).whi
      (parameters ⟨42,by decide⟩).wE (parameters ⟨42,by decide⟩).o
      (parameters ⟨42,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass52W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE52W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE52C {n : ℕ} (hn : 11883 ≤ n) {c : ℝ}
    (hc : B (206684003/500000000) (68497037/125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (68497037/125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (137449/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE52C (invN_bounds hn) hc) (by positivity)

theorem uniformNum52C {n : ℕ} (hn : 11883 ≤ n) :
    ta_num_sharp n (parameters ⟨42,by decide⟩).clo (parameters ⟨42,by decide⟩).chi
      (parameters ⟨42,by decide⟩).cE (parameters ⟨42,by decide⟩).o
      (parameters ⟨42,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass52C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE52C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

end BstLean.Part281.TI
