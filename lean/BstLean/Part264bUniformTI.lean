import BstLean.Part264bNormalizedE0
import BstLean.Part264bNormalizedE1
import BstLean.Part264bNormalizedE2
import BstLean.Part264bNormalizedE3
import BstLean.Part264bNormalizedO
import BstLean.Part264bSClasses
import BstLean.Part263Events
namespace BstLean.Part264b
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part246 BstLean.Part255

theorem uniformO {n : ℕ} (hn : 12227 ≤ n) :
    o3_kO n 46 ((mA n : ℝ)*(1/2+√23/n)) ((mA n : ℝ)*(1/2+√23/n)) ≤
      n * (33751/10^6) := by
  rw [norm_o (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedO (invN_bounds hn)) (by positivity)

theorem uniform_am_positive {n : ℕ} (hn : 12227 ≤ n) : 0 < s3am n 46 :=
  (uniformS0 hn (c := (69/200 : ℝ)) (by constructor <;> norm_num)).1
theorem uniformE10W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (50083597/125000000) (6825149/10000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (6825149/10000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (311219/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE10W (invN_bounds hn) hc) (by positivity)

theorem uniformNum10W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨0,by decide⟩).wlo (parameters ⟨0,by decide⟩).whi
      (parameters ⟨0,by decide⟩).wE (parameters ⟨0,by decide⟩).o
      (parameters ⟨0,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass10W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE10W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE10C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (58106111/125000000) (596791377/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (596791377/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (71709/125000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE10C (invN_bounds hn) hc) (by positivity)

theorem uniformNum10C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨0,by decide⟩).clo (parameters ⟨0,by decide⟩).chi
      (parameters ⟨0,by decide⟩).cE (parameters ⟨0,by decide⟩).o
      (parameters ⟨0,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass10C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE10C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE11W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (199723729/500000000) (340691301/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (340691301/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (621741/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE11W (invN_bounds hn) hc) (by positivity)

theorem uniformNum11W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨1,by decide⟩).wlo (parameters ⟨1,by decide⟩).whi
      (parameters ⟨1,by decide⟩).wE (parameters ⟨1,by decide⟩).o
      (parameters ⟨1,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass11W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE11W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE11C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (231820643/500000000) (595611421/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (595611421/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (11461/20000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE11C (invN_bounds hn) hc) (by positivity)

theorem uniformNum11C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨1,by decide⟩).clo (parameters ⟨1,by decide⟩).chi
      (parameters ⟨1,by decide⟩).cE (parameters ⟨1,by decide⟩).o
      (parameters ⟨1,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass11C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE11C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE12W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (398226781/1000000000) (136049893/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (136049893/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (310523/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE12W (invN_bounds hn) hc) (by positivity)

theorem uniformNum12W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨2,by decide⟩).wlo (parameters ⟨2,by decide⟩).whi
      (parameters ⟨2,by decide⟩).wE (parameters ⟨2,by decide⟩).o
      (parameters ⟨2,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass12W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE12W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE12C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (92486807/200000000) (118886213/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (118886213/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (572429/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE12C (invN_bounds hn) hc) (by positivity)

theorem uniformNum12C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨2,by decide⟩).clo (parameters ⟨2,by decide⟩).chi
      (parameters ⟨2,by decide⟩).cE (parameters ⟨2,by decide⟩).o
      (parameters ⟨2,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass12C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE12C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE13W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (79401349/200000000) (679115489/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (679115489/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (9693/15625) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE13W (invN_bounds hn) hc) (by positivity)

theorem uniformNum13W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨3,by decide⟩).wlo (parameters ⟨3,by decide⟩).whi
      (parameters ⟨3,by decide⟩).wE (parameters ⟨3,by decide⟩).o
      (parameters ⟨3,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass13W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE13W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE13C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (3603337/7812500) (593250309/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (593250309/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (571809/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE13C (invN_bounds hn) hc) (by positivity)

theorem uniformNum13C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨3,by decide⟩).clo (parameters ⟨3,by decide⟩).chi
      (parameters ⟨3,by decide⟩).cE (parameters ⟨3,by decide⟩).o
      (parameters ⟨3,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass13C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE13C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE14W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (395787347/1000000000) (677980677/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (677980677/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (619659/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE14W (invN_bounds hn) hc) (by positivity)

theorem uniformNum14W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨4,by decide⟩).wlo (parameters ⟨4,by decide⟩).whi
      (parameters ⟨4,by decide⟩).wE (parameters ⟨4,by decide⟩).o
      (parameters ⟨4,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass14W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE14W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE14C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (230010293/500000000) (592069153/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (592069153/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (57119/100000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE14C (invN_bounds hn) hc) (by positivity)

theorem uniformNum14C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨4,by decide⟩).clo (parameters ⟨4,by decide⟩).chi
      (parameters ⟨4,by decide⟩).cE (parameters ⟨4,by decide⟩).o
      (parameters ⟨4,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass14C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE14C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE15W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (197284293/500000000) (676845029/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (676845029/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (618967/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE15W (invN_bounds hn) hc) (by positivity)

theorem uniformNum15W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨5,by decide⟩).wlo (parameters ⟨5,by decide⟩).whi
      (parameters ⟨5,by decide⟩).wE (parameters ⟨5,by decide⟩).o
      (parameters ⟨5,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass15W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE15W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE15C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (229407193/500000000) (590887599/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (590887599/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (142643/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE15C (invN_bounds hn) hc) (by positivity)

theorem uniformNum15C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨5,by decide⟩).clo (parameters ⟨5,by decide⟩).chi
      (parameters ⟨5,by decide⟩).cE (parameters ⟨5,by decide⟩).o
      (parameters ⟨5,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass15C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE15C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE16W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (393350461/1000000000) (337854273/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (337854273/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (154569/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE16W (invN_bounds hn) hc) (by positivity)

theorem uniformNum16W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨6,by decide⟩).wlo (parameters ⟨6,by decide⟩).whi
      (parameters ⟨6,by decide⟩).wE (parameters ⟨6,by decide⟩).o
      (parameters ⟨6,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass16W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE16W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE16C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (228804267/500000000) (589705647/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (589705647/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (284977/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE16C (invN_bounds hn) hc) (by positivity)

theorem uniformNum16C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨6,by decide⟩).clo (parameters ⟨6,by decide⟩).chi
      (parameters ⟨6,by decide⟩).cE (parameters ⟨6,by decide⟩).o
      (parameters ⟨6,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass16C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE16C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE17W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (392132971/1000000000) (674571229/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (674571229/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (308793/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE17W (invN_bounds hn) hc) (by positivity)

theorem uniformNum17W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨7,by decide⟩).wlo (parameters ⟨7,by decide⟩).whi
      (parameters ⟨7,by decide⟩).wE (parameters ⟨7,by decide⟩).o
      (parameters ⟨7,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass17W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE17W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE17C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (456403031/1000000000) (588523297/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (588523297/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (284669/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE17C (invN_bounds hn) hc) (by positivity)

theorem uniformNum17C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨7,by decide⟩).clo (parameters ⟨7,by decide⟩).chi
      (parameters ⟨7,by decide⟩).cE (parameters ⟨7,by decide⟩).o
      (parameters ⟨7,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass17C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE17C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE18W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (195458057/500000000) (673433079/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (673433079/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (616897/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE18W (invN_bounds hn) hc) (by positivity)

theorem uniformNum18W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨8,by decide⟩).wlo (parameters ⟨8,by decide⟩).whi
      (parameters ⟨8,by decide⟩).wE (parameters ⟨8,by decide⟩).o
      (parameters ⟨8,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass18W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE18W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE18C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (113799469/250000000) (11746811/20000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (11746811/20000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (568723/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE18C (invN_bounds hn) hc) (by positivity)

theorem uniformNum18C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨8,by decide⟩).clo (parameters ⟨8,by decide⟩).chi
      (parameters ⟨8,by decide⟩).cE (parameters ⟨8,by decide⟩).o
      (parameters ⟨8,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass18C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE18C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE19W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (389699889/1000000000) (336147049/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (336147049/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (616209/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE19W (invN_bounds hn) hc) (by positivity)

theorem uniformNum19W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨9,by decide⟩).wlo (parameters ⟨9,by decide⟩).whi
      (parameters ⟨9,by decide⟩).wE (parameters ⟨9,by decide⟩).o
      (parameters ⟨9,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass19W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE19W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE19C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (113498267/250000000) (586157407/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (586157407/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (568109/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE19C (invN_bounds hn) hc) (by positivity)

theorem uniformNum19C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨9,by decide⟩).clo (parameters ⟨9,by decide⟩).chi
      (parameters ⟨9,by decide⟩).cE (parameters ⟨9,by decide⟩).o
      (parameters ⟨9,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass19C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE19C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE20W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (77696859/200000000) (335577143/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (335577143/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (307761/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE20W (invN_bounds hn) hc) (by positivity)

theorem uniformNum20W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨10,by decide⟩).wlo (parameters ⟨10,by decide⟩).whi
      (parameters ⟨10,by decide⟩).wE (parameters ⟨10,by decide⟩).o
      (parameters ⟨10,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass20W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE20W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE20C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (226394303/500000000) (584973867/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (584973867/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (70937/125000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE20C (invN_bounds hn) hc) (by positivity)

theorem uniformNum20C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨10,by decide⟩).clo (parameters ⟨10,by decide⟩).chi
      (parameters ⟨10,by decide⟩).cE (parameters ⟨10,by decide⟩).o
      (parameters ⟨10,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass20C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE20C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE21W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (38726933/100000000) (134002729/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (134002729/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (153709/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE21W (invN_bounds hn) hc) (by positivity)

theorem uniformNum21W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨11,by decide⟩).wlo (parameters ⟨11,by decide⟩).whi
      (parameters ⟨11,by decide⟩).wE (parameters ⟨11,by decide⟩).o
      (parameters ⟨11,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass21W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE21W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE21C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (45158449/100000000) (145947483/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (145947483/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (566883/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE21C (invN_bounds hn) hc) (by positivity)

theorem uniformNum21C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨11,by decide⟩).clo (parameters ⟨11,by decide⟩).chi
      (parameters ⟨11,by decide⟩).cE (parameters ⟨11,by decide⟩).o
      (parameters ⟨11,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass21C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE21C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE22W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (386054993/1000000000) (26754887/40000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (26754887/40000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (76769/125000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE22W (invN_bounds hn) hc) (by positivity)

theorem uniformNum22W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨12,by decide⟩).wlo (parameters ⟨12,by decide⟩).whi
      (parameters ⟨12,by decide⟩).wE (parameters ⟨12,by decide⟩).o
      (parameters ⟨12,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass22W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE22W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE22C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (450380719/1000000000) (291302801/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (291302801/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (8848/15625) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE22C (invN_bounds hn) hc) (by positivity)

theorem uniformNum22C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨12,by decide⟩).clo (parameters ⟨12,by decide⟩).chi
      (parameters ⟨12,by decide⟩).cE (parameters ⟨12,by decide⟩).o
      (parameters ⟨12,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass22C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE22C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE23W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (192420641/500000000) (667729877/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (667729877/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (153367/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE23W (invN_bounds hn) hc) (by positivity)

theorem uniformNum23W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨13,by decide⟩).wlo (parameters ⟨13,by decide⟩).whi
      (parameters ⟨13,by decide⟩).wE (parameters ⟨13,by decide⟩).o
      (parameters ⟨13,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass23W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE23W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE23C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (112294323/250000000) (290710439/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (290710439/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (565661/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE23C (invN_bounds hn) hc) (by positivity)

theorem uniformNum23C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨13,by decide⟩).clo (parameters ⟨13,by decide⟩).chi
      (parameters ⟨13,by decide⟩).cE (parameters ⟨13,by decide⟩).o
      (parameters ⟨13,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass23C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE23C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE24W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (383628197/1000000000) (666586753/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (666586753/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (122557/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE24W (invN_bounds hn) hc) (by positivity)

theorem uniformNum24W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨14,by decide⟩).wlo (parameters ⟨14,by decide⟩).whi
      (parameters ⟨14,by decide⟩).wE (parameters ⟨14,by decide⟩).o
      (parameters ⟨14,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass24W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE24W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE24C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (44797421/100000000) (7252947/12500000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (7252947/12500000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (141263/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE24C (invN_bounds hn) hc) (by positivity)

theorem uniformNum24C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨14,by decide⟩).clo (parameters ⟨14,by decide⟩).chi
      (parameters ⟨14,by decide⟩).cE (parameters ⟨14,by decide⟩).o
      (parameters ⟨14,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass24C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE24C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE25W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (47801967/125000000) (166360701/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (166360701/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (612103/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE25W (invN_bounds hn) hc) (by positivity)

theorem uniformNum25W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨15,by decide⟩).wlo (parameters ⟨15,by decide⟩).whi
      (parameters ⟨15,by decide⟩).wE (parameters ⟨15,by decide⟩).o
      (parameters ⟨15,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass25W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE25W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE25C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (446771471/1000000000) (72381281/125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (72381281/125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (564443/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE25C (invN_bounds hn) hc) (by positivity)

theorem uniformNum25C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨15,by decide⟩).clo (parameters ⟨15,by decide⟩).chi
      (parameters ⟨15,by decide⟩).cE (parameters ⟨15,by decide⟩).o
      (parameters ⟨15,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass25C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE25C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE26W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (190601949/500000000) (66429803/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (66429803/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (305711/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE26W (invN_bounds hn) hc) (by positivity)

theorem uniformNum26W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨16,by decide⟩).wlo (parameters ⟨16,by decide⟩).whi
      (parameters ⟨16,by decide⟩).wE (parameters ⟨16,by decide⟩).o
      (parameters ⟨16,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass26W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE26W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE26C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (17822763/40000000) (577864343/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (577864343/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (112767/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE26C (invN_bounds hn) hc) (by positivity)

theorem uniformNum26C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨16,by decide⟩).clo (parameters ⟨16,by decide⟩).chi
      (parameters ⟨16,by decide⟩).cE (parameters ⟨16,by decide⟩).o
      (parameters ⟨16,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass26C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE26C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE27W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (189996341/500000000) (41447027/62500000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (41447027/62500000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (610743/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE27W (invN_bounds hn) hc) (by positivity)

theorem uniformNum27W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨17,by decide⟩).wlo (parameters ⟨17,by decide⟩).whi
      (parameters ⟨17,by decide⟩).wE (parameters ⟨17,by decide⟩).o
      (parameters ⟨17,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass27W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE27W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE27C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (444367021/1000000000) (288339023/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (288339023/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (140807/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE27C (invN_bounds hn) hc) (by positivity)

theorem uniformNum27C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨17,by decide⟩).clo (parameters ⟨17,by decide⟩).chi
      (parameters ⟨17,by decide⟩).cE (parameters ⟨17,by decide⟩).o
      (parameters ⟨17,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass27C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE27C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE28W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (75756417/200000000) (165501503/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (165501503/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (38129/62500) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE28W (invN_bounds hn) hc) (by positivity)

theorem uniformNum28W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨18,by decide⟩).wlo (parameters ⟨18,by decide⟩).whi
      (parameters ⟨18,by decide⟩).wE (parameters ⟨18,by decide⟩).o
      (parameters ⟨18,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass28W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE28W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE28C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (443165309/1000000000) (575491357/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (575491357/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (281311/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE28C (invN_bounds hn) hc) (by positivity)

theorem uniformNum28C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨18,by decide⟩).clo (parameters ⟨18,by decide⟩).chi
      (parameters ⟨18,by decide⟩).cE (parameters ⟨18,by decide⟩).o
      (parameters ⟨18,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass28C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE28C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE29W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (94393027/250000000) (66085877/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (66085877/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (304693/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE29W (invN_bounds hn) hc) (by positivity)

theorem uniformNum29W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨19,by decide⟩).wlo (parameters ⟨19,by decide⟩).whi
      (parameters ⟨19,by decide⟩).wE (parameters ⟨19,by decide⟩).o
      (parameters ⟨19,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass29W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE29W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE29C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (220981969/500000000) (574304277/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (574304277/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (562017/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE29C (invN_bounds hn) hc) (by positivity)

theorem uniformNum29C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨19,by decide⟩).clo (parameters ⟨19,by decide⟩).chi
      (parameters ⟨19,by decide⟩).cE (parameters ⟨19,by decide⟩).o
      (parameters ⟨19,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass29C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE29C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE30W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (376362749/1000000000) (659710707/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (659710707/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (608709/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE30W (invN_bounds hn) hc) (by positivity)

theorem uniformNum30W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨20,by decide⟩).wlo (parameters ⟨20,by decide⟩).whi
      (parameters ⟨20,by decide⟩).wE (parameters ⟨20,by decide⟩).o
      (parameters ⟨20,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass30W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE30W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE30C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (440762907/1000000000) (286558403/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (286558403/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (561413/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE30C (invN_bounds hn) hc) (by positivity)

theorem uniformNum30C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨20,by decide⟩).clo (parameters ⟨20,by decide⟩).chi
      (parameters ⟨20,by decide⟩).cE (parameters ⟨20,by decide⟩).o
      (parameters ⟨20,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass30C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE30C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE31W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (375154007/1000000000) (26342473/40000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (26342473/40000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (304017/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE31W (invN_bounds hn) hc) (by positivity)

theorem uniformNum31W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨21,by decide⟩).wlo (parameters ⟨21,by decide⟩).whi
      (parameters ⟨21,by decide⟩).wE (parameters ⟨21,by decide⟩).o
      (parameters ⟨21,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass31W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE31W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE31C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (439562217/1000000000) (35745559/62500000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (35745559/62500000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (56081/100000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE31C (invN_bounds hn) hc) (by positivity)

theorem uniformNum31C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨21,by decide⟩).clo (parameters ⟨21,by decide⟩).chi
      (parameters ⟨21,by decide⟩).cE (parameters ⟨21,by decide⟩).o
      (parameters ⟨21,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass31C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE31C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE32W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (9348647/25000000) (164353031/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (164353031/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (607359/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE32W (invN_bounds hn) hc) (by positivity)

theorem uniformNum32W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨22,by decide⟩).wlo (parameters ⟨22,by decide⟩).whi
      (parameters ⟨22,by decide⟩).wE (parameters ⟨22,by decide⟩).o
      (parameters ⟨22,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass32W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE32W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE32C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (87672373/200000000) (142685173/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (142685173/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (35013/62500) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE32C (invN_bounds hn) hc) (by positivity)

theorem uniformNum32C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨22,by decide⟩).clo (parameters ⟨22,by decide⟩).chi
      (parameters ⟨22,by decide⟩).cE (parameters ⟨22,by decide⟩).o
      (parameters ⟨22,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass32C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE32C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE33W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (372738367/1000000000) (328130803/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (328130803/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (121337/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE33W (invN_bounds hn) hc) (by positivity)

theorem uniformNum33W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨23,by decide⟩).wlo (parameters ⟨23,by decide⟩).whi
      (parameters ⟨23,by decide⟩).wE (parameters ⟨23,by decide⟩).o
      (parameters ⟨23,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass33W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE33W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE33C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (437161853/1000000000) (569552051/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (569552051/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (279803/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE33C (invN_bounds hn) hc) (by positivity)

theorem uniformNum33C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨23,by decide⟩).clo (parameters ⟨23,by decide⟩).chi
      (parameters ⟨23,by decide⟩).cE (parameters ⟨23,by decide⟩).o
      (parameters ⟨23,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass33C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE33C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE34W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (371531467/1000000000) (65511027/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (65511027/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (151503/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE34W (invN_bounds hn) hc) (by positivity)

theorem uniformNum34W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨24,by decide⟩).wlo (parameters ⟨24,by decide⟩).whi
      (parameters ⟨24,by decide⟩).wE (parameters ⟨24,by decide⟩).o
      (parameters ⟨24,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass34W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE34W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE34C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (217981089/500000000) (568363021/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (568363021/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (279503/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE34C (invN_bounds hn) hc) (by positivity)

theorem uniformNum34C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨24,by decide⟩).clo (parameters ⟨24,by decide⟩).chi
      (parameters ⟨24,by decide⟩).cE (parameters ⟨24,by decide⟩).o
      (parameters ⟨24,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass34C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE34C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE35W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (370325179/1000000000) (653958119/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (653958119/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (30267/50000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE35W (invN_bounds hn) hc) (by positivity)

theorem uniformNum35W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨25,by decide⟩).wlo (parameters ⟨25,by decide⟩).whi
      (parameters ⟨25,by decide⟩).wE (parameters ⟨25,by decide⟩).o
      (parameters ⟨25,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass35W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE35W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE35C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (217381421/500000000) (567173603/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (567173603/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (279203/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE35C (invN_bounds hn) hc) (by positivity)

theorem uniformNum35C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨25,by decide⟩).clo (parameters ⟨25,by decide⟩).chi
      (parameters ⟨25,by decide⟩).cE (parameters ⟨25,by decide⟩).o
      (parameters ⟨25,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass35C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE35C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE36W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (184559751/500000000) (652805153/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (652805153/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (604669/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE36W (invN_bounds hn) hc) (by positivity)

theorem uniformNum36W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨26,by decide⟩).wlo (parameters ⟨26,by decide⟩).whi
      (parameters ⟨26,by decide⟩).wE (parameters ⟨26,by decide⟩).o
      (parameters ⟨26,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass36W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE36W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE36C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (216781921/500000000) (141495949/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (141495949/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (34863/62500) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE36C (invN_bounds hn) hc) (by positivity)

theorem uniformNum36C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨26,by decide⟩).clo (parameters ⟨26,by decide⟩).chi
      (parameters ⟨26,by decide⟩).cE (parameters ⟨26,by decide⟩).o
      (parameters ⟨26,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass36C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE36C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE37W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (183957217/500000000) (162912843/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (162912843/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (603999/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE37W (invN_bounds hn) hc) (by positivity)

theorem uniformNum37W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨27,by decide⟩).wlo (parameters ⟨27,by decide⟩).whi
      (parameters ⟨27,by decide⟩).wE (parameters ⟨27,by decide⟩).o
      (parameters ⟨27,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass37W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE37W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE37C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (21618259/50000000) (282396801/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (282396801/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (55721/100000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE37C (invN_bounds hn) hc) (by positivity)

theorem uniformNum37C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨27,by decide⟩).clo (parameters ⟨27,by decide⟩).chi
      (parameters ⟨27,by decide⟩).cE (parameters ⟨27,by decide⟩).o
      (parameters ⟨27,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass37C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE37C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE38W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (183354987/500000000) (325248389/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (325248389/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (60333/100000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE38W (invN_bounds hn) hc) (by positivity)

theorem uniformNum38W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨28,by decide⟩).wlo (parameters ⟨28,by decide⟩).whi
      (parameters ⟨28,by decide⟩).wE (parameters ⟨28,by decide⟩).o
      (parameters ⟨28,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass38W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE38W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE38C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (431166853/1000000000) (28180151/50000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (28180151/50000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (556613/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE38C (invN_bounds hn) hc) (by positivity)

theorem uniformNum38C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨28,by decide⟩).clo (parameters ⟨28,by decide⟩).chi
      (parameters ⟨28,by decide⟩).cE (parameters ⟨28,by decide⟩).o
      (parameters ⟨28,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass38C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE38C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE39W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (182753061/500000000) (162335343/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (162335343/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (301331/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE39W (invN_bounds hn) hc) (by positivity)

theorem uniformNum39W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨29,by decide⟩).wlo (parameters ⟨29,by decide⟩).whi
      (parameters ⟨29,by decide⟩).wE (parameters ⟨29,by decide⟩).o
      (parameters ⟨29,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass39W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE39W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE39C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (214984431/500000000) (140603013/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (140603013/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (556017/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE39C (invN_bounds hn) hc) (by positivity)

theorem uniformNum39C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨29,by decide⟩).clo (parameters ⟨29,by decide⟩).chi
      (parameters ⟨29,by decide⟩).cE (parameters ⟨29,by decide⟩).o
      (parameters ⟨29,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass39C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE39C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE40W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (2914423/8000000) (129637031/200000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (129637031/200000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (120399/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE40W (invN_bounds hn) hc) (by positivity)

theorem uniformNum40W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨30,by decide⟩).wlo (parameters ⟨30,by decide⟩).whi
      (parameters ⟨30,by decide⟩).wE (parameters ⟨30,by decide⟩).o
      (parameters ⟨30,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass40W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE40W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE40C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (85754241/200000000) (280610349/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (280610349/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (555421/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE40C (invN_bounds hn) hc) (by positivity)

theorem uniformNum40C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨30,by decide⟩).clo (parameters ⟨30,by decide⟩).chi
      (parameters ⟨30,by decide⟩).cE (parameters ⟨30,by decide⟩).o
      (parameters ⟨30,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass40C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE40C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE41W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (181550117/500000000) (647028127/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (647028127/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (601329/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE41W (invN_bounds hn) hc) (by positivity)

theorem uniformNum41W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨31,by decide⟩).wlo (parameters ⟨31,by decide⟩).whi
      (parameters ⟨31,by decide⟩).wE (parameters ⟨31,by decide⟩).o
      (parameters ⟨31,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass41W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE41W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE41C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (106893471/250000000) (280014479/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (280014479/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (554827/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE41C (invN_bounds hn) hc) (by positivity)

theorem uniformNum41C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨31,by decide⟩).clo (parameters ⟨31,by decide⟩).chi
      (parameters ⟨31,by decide⟩).cE (parameters ⟨31,by decide⟩).o
      (parameters ⟨31,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass41C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE41C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE42W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (90474549/250000000) (64587029/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (64587029/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (75083/125000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE42W (invN_bounds hn) hc) (by positivity)

theorem uniformNum42W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨32,by decide⟩).wlo (parameters ⟨32,by decide⟩).whi
      (parameters ⟨32,by decide⟩).wE (parameters ⟨32,by decide⟩).o
      (parameters ⟨32,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass42W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE42W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE42C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (6662139/15625000) (17463651/31250000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (17463651/31250000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (277117/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE42C (invN_bounds hn) hc) (by positivity)

theorem uniformNum42C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨32,by decide⟩).clo (parameters ⟨32,by decide⟩).chi
      (parameters ⟨32,by decide⟩).cE (parameters ⟨32,by decide⟩).o
      (parameters ⟨32,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass42C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE42C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE43W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (360696761/1000000000) (644711643/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (644711643/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (599999/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE43W (invN_bounds hn) hc) (by positivity)

theorem uniformNum43W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨33,by decide⟩).wlo (parameters ⟨33,by decide⟩).whi
      (parameters ⟨33,by decide⟩).wE (parameters ⟨33,by decide⟩).o
      (parameters ⟨33,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass43W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE43W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE43C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (425180241/1000000000) (278822161/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (278822161/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (553641/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE43C (invN_bounds hn) hc) (by positivity)

theorem uniformNum43C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨33,by decide⟩).clo (parameters ⟨33,by decide⟩).chi
      (parameters ⟨33,by decide⟩).cE (parameters ⟨33,by decide⟩).o
      (parameters ⟨33,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass43C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE43C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE44W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (359495927/1000000000) (643552189/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (643552189/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (74917/125000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE44W (invN_bounds hn) hc) (by positivity)

theorem uniformNum44W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨34,by decide⟩).wlo (parameters ⟨34,by decide⟩).whi
      (parameters ⟨34,by decide⟩).wE (parameters ⟨34,by decide⟩).o
      (parameters ⟨34,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass44W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE44W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE44C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (5299799/12500000) (556451427/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (556451427/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (553049/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE44C (invN_bounds hn) hc) (by positivity)

theorem uniformNum44C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨34,by decide⟩).clo (parameters ⟨34,by decide⟩).chi
      (parameters ⟨34,by decide⟩).cE (parameters ⟨34,by decide⟩).o
      (parameters ⟨34,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass44C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE44C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE45W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (358295693/1000000000) (80298991/125000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (80298991/125000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (299337/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE45W (invN_bounds hn) hc) (by positivity)

theorem uniformNum45W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨35,by decide⟩).wlo (parameters ⟨35,by decide⟩).whi
      (parameters ⟨35,by decide⟩).wE (parameters ⟨35,by decide⟩).o
      (parameters ⟨35,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass45W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE45W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE45C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (42278793/100000000) (138814537/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (138814537/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (276229/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE45C (invN_bounds hn) hc) (by positivity)

theorem uniformNum45C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨35,by decide⟩).clo (parameters ⟨35,by decide⟩).chi
      (parameters ⟨35,by decide⟩).cE (parameters ⟨35,by decide⟩).o
      (parameters ⟨35,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass45C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE45C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE46W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (357096059/1000000000) (32061543/50000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (32061543/50000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (149503/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE46W (invN_bounds hn) hc) (by positivity)

theorem uniformNum46W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨36,by decide⟩).wlo (parameters ⟨36,by decide⟩).whi
      (parameters ⟨36,by decide⟩).wE (parameters ⟨36,by decide⟩).o
      (parameters ⟨36,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass46W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE46W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE46C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (421592273/1000000000) (277032243/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (277032243/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (137967/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE46C (invN_bounds hn) hc) (by positivity)

theorem uniformNum46C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨36,by decide⟩).clo (parameters ⟨36,by decide⟩).chi
      (parameters ⟨36,by decide⟩).cE (parameters ⟨36,by decide⟩).o
      (parameters ⟨36,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass46C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE46C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE47W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (355897023/1000000000) (640068987/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (640068987/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (74669/125000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE47W (invN_bounds hn) hc) (by positivity)

theorem uniformNum47W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨37,by decide⟩).wlo (parameters ⟨37,by decide⟩).whi
      (parameters ⟨37,by decide⟩).wE (parameters ⟨37,by decide⟩).o
      (parameters ⟨37,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass47W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE47W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE47C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (420396947/1000000000) (552870441/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (552870441/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (551279/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE47C (invN_bounds hn) hc) (by positivity)

theorem uniformNum47C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨37,by decide⟩).clo (parameters ⟨37,by decide⟩).chi
      (parameters ⟨37,by decide⟩).cE (parameters ⟨37,by decide⟩).o
      (parameters ⟨37,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass47C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE47C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE48W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (44337323/125000000) (63890631/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (63890631/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (149173/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE48W (invN_bounds hn) hc) (by positivity)

theorem uniformNum48W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨38,by decide⟩).wlo (parameters ⟨38,by decide⟩).whi
      (parameters ⟨38,by decide⟩).wE (parameters ⟨38,by decide⟩).o
      (parameters ⟨38,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass48W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE48W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE48C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (13100061/31250000) (137919003/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (137919003/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (550691/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE48C (invN_bounds hn) hc) (by positivity)

theorem uniformNum48C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨38,by decide⟩).clo (parameters ⟨38,by decide⟩).chi
      (parameters ⟨38,by decide⟩).cE (parameters ⟨38,by decide⟩).o
      (parameters ⟨38,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass48C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE48C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE49W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (353500741/1000000000) (159435707/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (159435707/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (596033/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE49W (invN_bounds hn) hc) (by positivity)

theorem uniformNum49W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨39,by decide⟩).wlo (parameters ⟨39,by decide⟩).whi
      (parameters ⟨39,by decide⟩).wE (parameters ⟨39,by decide⟩).o
      (parameters ⟨39,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass49W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE49W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE49C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (418007287/1000000000) (275240601/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (275240601/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (550103/1000000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE49C (invN_bounds hn) hc) (by positivity)

theorem uniformNum49C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨39,by decide⟩).clo (parameters ⟨39,by decide⟩).chi
      (parameters ⟨39,by decide⟩).cE (parameters ⟨39,by decide⟩).o
      (parameters ⟨39,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass49C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE49C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE50W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (352303493/1000000000) (39786159/62500000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (39786159/62500000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (4763/8000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE50W (invN_bounds hn) hc) (by positivity)

theorem uniformNum50W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨40,by decide⟩).wlo (parameters ⟨40,by decide⟩).whi
      (parameters ⟨40,by decide⟩).wE (parameters ⟨40,by decide⟩).o
      (parameters ⟨40,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass50W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE50W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE50C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (52101619/125000000) (54928601/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (54928601/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (137379/250000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE50C (invN_bounds hn) hc) (by positivity)

theorem uniformNum50C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨40,by decide⟩).clo (parameters ⟨40,by decide⟩).chi
      (parameters ⟨40,by decide⟩).cE (parameters ⟨40,by decide⟩).o
      (parameters ⟨40,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass50C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE50C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE51W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (351106839/1000000000) (317706729/500000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (317706729/500000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (297359/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE51W (invN_bounds hn) hc) (by positivity)

theorem uniformNum51W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨41,by decide⟩).wlo (parameters ⟨41,by decide⟩).whi
      (parameters ⟨41,by decide⟩).wE (parameters ⟨41,by decide⟩).o
      (parameters ⟨41,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass51W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE51W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE51C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (207809473/500000000) (137022609/250000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (137022609/250000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (54893/100000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE51C (invN_bounds hn) hc) (by positivity)

theorem uniformNum51C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨41,by decide⟩).clo (parameters ⟨41,by decide⟩).chi
      (parameters ⟨41,by decide⟩).cE (parameters ⟨41,by decide⟩).o
      (parameters ⟨41,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass51C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE51C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE52W {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (349910777/1000000000) (63424757/100000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (63424757/100000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (297031/500000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE52W (invN_bounds hn) hc) (by positivity)

theorem uniformNum52W {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨42,by decide⟩).wlo (parameters ⟨42,by decide⟩).whi
      (parameters ⟨42,by decide⟩).wE (parameters ⟨42,by decide⟩).o
      (parameters ⟨42,by decide⟩).wS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass52W hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE52W hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem uniformE52C {n : ℕ} (hn : 12227 ≤ n) {c : ℝ}
    (hc : B (414425269/1000000000) (546894481/1000000000) c) :
    e3s_bound n ((mA n : ℝ)*(kdot (s3c1 n 46 c)/2+√23/n)) (√(2*46))
      (e4_b n ((mA n : ℝ)*(1/2+√23/n)) 46)
      (e4_b n ((mA n : ℝ)*(kdot (546894481/1000000000)/2+√23/n)) 46^2)
      (e4_b n 2 46) ≤ n * (109669/200000) := by
  rw [e3_normalized (by omega : 0 < n)]
  exact mul_le_mul_of_nonneg_left (normalizedE52C (invN_bounds hn) hc) (by positivity)

theorem uniformNum52C {n : ℕ} (hn : 12227 ≤ n) :
    ta_num_sharp n (parameters ⟨42,by decide⟩).clo (parameters ⟨42,by decide⟩).chi
      (parameters ⟨42,by decide⟩).cE (parameters ⟨42,by decide⟩).o
      (parameters ⟨42,by decide⟩).cS (BstLean.Part263.maskSlack n) 46 := by
  refine ⟨by convert uniformO hn using 1 <;> norm_num [parameters,BstLean.Part263.maskSlack],
    uniform_am_positive hn,?_⟩
  intro c hlo hhi
  have hs := sClass52C hn (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    uniformE52C hn ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

end BstLean.Part264b
