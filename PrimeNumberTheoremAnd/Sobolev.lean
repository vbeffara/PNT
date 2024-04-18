import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators

attribute [fun_prop] Integrable Integrable.norm Integrable.const_mul Integrable.add
attribute [fun_prop] AEStronglyMeasurable Continuous.aestronglyMeasurable
attribute [fun_prop] HasCompactSupport HasCompactSupport.smul_right HasCompactSupport.smul_right HasCompactSupport.mul_left

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CD (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] extends CD n E where
  compact : HasCompactSupport toFun

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] extends CD n E where
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ⊤ ofReal' := by
  have key x : HasDerivAt ofReal' 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal' = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_top_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CD

variable {f : CD n E} {R x v : ℝ}

instance : CoeFun (CD n E) (fun _ => ℝ → E) where coe f := f.toFun

instance : Coe (CD n ℝ) (CD n ℂ) where coe f := ⟨ofReal' ∘ f, contDiff_ofReal.of_le le_top |>.comp f.smooth⟩

def of_le (f : CD n E) {m : ℕ} (hm : m ≤ n) : CD m E := ⟨f, f.smooth.of_le (by simp [hm])⟩

def neg (f : CD n E) : CD n E := ⟨-f, f.smooth.neg⟩

instance : Neg (CD n E) where neg := neg

def smul (R : ℝ) (f : CD n E) : CD n E := ⟨R • f, f.smooth.const_smul R⟩

instance : HSMul ℝ (CD n E) (CD n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

@[continuity, fun_prop] lemma continuous (f : CD n E) : Continuous f := f.smooth.continuous

noncomputable nonrec def deriv (f : CD (n + 1) E) : CD n E := ⟨deriv f, (contDiff_succ_iff_deriv.mp f.smooth).2⟩

lemma hasDerivAt (f : CD (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.smooth.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CD (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

lemma deriv_smul {f : CD (n + 1) E} : (R • f).deriv = R • f.deriv := by
  ext x ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CD n E) (R : ℝ) : CD n E := by
  by_cases R = 0
  · exact ⟨0, contDiff_const⟩
  · exact ⟨funscale g R, g.smooth.comp (contDiff_const.smul contDiff_id)⟩

lemma deriv_scale {f : CD (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  ext v ; by_cases hR : R = 0 <;> simp [hR, scale]
  · simp [deriv, smul] ; exact deriv_const _ _
  · exact ((f.hasDerivAt (R⁻¹ • v)).scomp v (by simpa using (hasDerivAt_id v).const_smul R⁻¹)).deriv

@[simp] lemma deriv_scale' {f : CD (n + 1) E} : (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale] ; by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CD (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • f.deriv (R⁻¹ • x)) x := by
  simpa using hasDerivAt (f.scale R) x

lemma tendsto_scale (f : CD n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

end CD

namespace CS

variable {f : CS n E} {R x v : ℝ}

lemma ext_CD {f g : CS n E} (h : f.toCD = g.toCD) : f = g := by
  cases f ; cases g ; simp ; exact h

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe f := f.toFun

instance : Coe (CS n E) (CD n E) where coe := toCD

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨f, f.compact.comp_left (g := ofReal') rfl⟩

nonrec def of_le (f : CS n E) {m : ℕ} (hm : m ≤ n) : CS m E := ⟨f.of_le hm, f.compact⟩

instance {k : ℕ} : CoeOut (CS (n + k) E) (CS n E) where coe f := f.of_le (by simp)

@[simp] lemma neg_toFun : (-f.toCD).toFun = -(f.toFun) := rfl

def neg (f : CS n E) : CS n E := ⟨-f, by simpa [HasCompactSupport, tsupport] using f.compact⟩

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.compact.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

noncomputable nonrec def deriv (f : CS (n + 1) E) : CS n E := ⟨f.deriv, f.compact.deriv⟩

nonrec lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x := f.hasDerivAt x

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := CD.deriv_apply

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  ext x ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable nonrec def scale (g : CS n E) (R : ℝ) : CS n E := by
  refine ⟨g.scale R, ?_⟩
  by_cases h : R = 0 <;> simp [CD.scale, h]
  · simp [HasCompactSupport, tsupport]
  · exact g.compact.comp_smul (inv_ne_zero h)

nonrec lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  apply ext_CD ; exact CD.deriv_scale

@[simp] lemma deriv_scale' {f : CS (n + 1) E} : (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := CD.deriv_scale'

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • f.deriv (R⁻¹ • x)) x := CD.hasDerivAt_scale _ _ _

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := CD.tendsto_scale _ _

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ := (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.compact.norm
  refine ⟨_, hx⟩

lemma integrable (f : CS n E) : Integrable f := f.continuous.integrable_of_hasCompactSupport f.compact

lemma integrable_iteratedDeriv {n : ℕ} (f : CS n E) : Integrable (iteratedDeriv n f) := by
  induction n with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using ih f.deriv

lemma integrable_iteratedDeriv_of_le {n : ℕ} (f : CS n E) ⦃k : ℕ⦄ (hk : k ≤ n) : Integrable (iteratedDeriv k f) := by
  obtain ⟨m, rfl⟩ := Nat.le.dest hk ; exact (f : CS k E).integrable_iteratedDeriv

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 := (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe f := f.toFun

@[fun_prop] lemma integrable' (f : W1 n E) : Integrable f := f.integrable (zero_le n)

@[fun_prop, continuity] lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toCD := f.toCD.deriv
  integrable k hk := by simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x := f.toCD.hasDerivAt _

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using ih (f := SchwartzMap.derivCLM ℝ f)

def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

instance : Coe (CS n E) (W1 n E) where coe f := ⟨f.toCD, f.integrable_iteratedDeriv_of_le⟩

instance : HMul (CS n ℝ) (W1 n E) (CS n E) where hMul g f :=
  ⟨⟨⇑g • f, g.smooth.smul f.smooth⟩, g.compact.smul_right⟩

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm f := norm f

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

instance : Coe (CS 2 ℂ) W21 where coe := fun f => f

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where hMul g f := ⟨⟨g * f, g.smooth.mul f.smooth⟩, g.compact.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

end W21

lemma approx_aux1 {f : ℝ → E} {g : ℝ → ℝ} (h1 : Integrable f) (h2 : ∀ x, |g x| ≤ 1)
    (h3 : Continuous g) (h4 : g 0 = 1) :
    Tendsto (fun R => ∫ x, funscale g R x • f x) atTop (𝓝 (∫ x, f x)) := by

  let F R x : E := funscale g R x • f x
  have l1 : ∀ᶠ R in atTop, AEStronglyMeasurable (F R) := by
    apply eventually_of_forall ; intro R
    exact (h3.comp (by continuity)).aestronglyMeasurable.smul h1.1
  have l2 : ∀ᶠ R in atTop, ∀ᵐ x, ‖F R x‖ ≤ ‖f x‖ := by
    apply eventually_of_forall ; intro R ; apply eventually_of_forall ; intro x
    simp [F, funscale, norm_smul]
    convert_to _ ≤ 1 * ‖f x‖ ; simp
    have := h2 (R⁻¹ * x) ; gcongr
  have l4 : ∀ᵐ x, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x)) := by
    apply eventually_of_forall ; intro x
    simpa [h4] using (tendsto_funscale h3.continuousAt x).smul_const (f x)
  exact tendsto_integral_filter_of_dominated_convergence _ l1 l2 h1.norm l4

lemma approx_aux2 {f : ℝ → E} {g : ℝ → ℝ} (h1 : Integrable f)
    (h2 : ∀ x, g x ≤ 1) (h2' : ∀ x, 0 ≤ g x) (h3 : Continuous g) (h4 : g 0 = 1) :
    Tendsto (fun R => ∫ x, ‖(1 - funscale g R x) • f x‖) atTop (𝓝 0) := by

  let F R x : ℝ := ‖(1 - funscale g R x) • f x‖
  have l1 : ∀ᶠ R in atTop, AEStronglyMeasurable (F R) := by
    apply eventually_of_forall ; intro R
    exact ((aestronglyMeasurable_const.sub ((h3.comp (by continuity)).aestronglyMeasurable)).smul h1.1).norm
  have l2 : ∀ᶠ R in atTop, ∀ᵐ x, ‖F R x‖ ≤ ‖f x‖ := by
    apply eventually_of_forall ; intro R ; apply eventually_of_forall ; intro x
    convert_to |1 - g (R⁻¹ * x)| * ‖f x‖ ≤ 1 * ‖f x‖ ; simp [F, funscale, norm_smul] ; simp
    gcongr ; rw [abs_le] ; constructor <;> linarith [h2 (R⁻¹ * x), h2' (R⁻¹ * x)]
  have l4 : ∀ᵐ x, Tendsto (fun n ↦ F n x) atTop (𝓝 0) := by
    apply eventually_of_forall ; intro x
    simpa [h4] using tendsto_funscale h3.continuousAt x |>.const_sub 1 |>.smul_const (f x) |>.norm
  simpa [F] using tendsto_integral_filter_of_dominated_convergence _ l1 l2 h1.norm l4

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Setup
  let G R : CS 2 ℝ := g.scale R ; let h R v := 1 - G R v
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl

  -- Take care of the first piece
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  have piece_1 : Tendsto (fun R ↦ ∫ v, ‖h R v * f v‖) atTop (𝓝 0) := by
    apply approx_aux2 f.integrable' g.le_one g.nonneg g.continuous g.zero_at |>.congr'
    filter_upwards [eventually_ne_atTop 0] with R hR ; simp [h, G, CS.scale, CD.scale, hR]
  refine piece_1.add (Tendsto.const_mul _ ?_) ; clear piece_1

  -- Definitions
  let f' := f.deriv ; let f'' := f'.deriv
  let G' R := (G R).deriv ; let G'' R := (G' R).deriv
  let F R v := ‖- G'' R v * f v + 2 * -G' R v * f' v + h R v * f'' v‖

  -- Proof
  convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
  · ext R ; congr ; ext v ; congr ; apply HasDerivAt.deriv
    have dh v : HasDerivAt (h R) (-G' R v) v := by
      simpa [G', G] using (g : CS 2 ℝ).hasDerivAt_scale R v |>.const_sub 1
    have l5 := ((G' R).hasDerivAt v).ofReal_comp.neg.mul (f.hasDerivAt v)
    have l7 := (dh v).ofReal_comp.mul (f'.hasDerivAt v)
    have d1 : deriv _ = _ := funext (fun v => ((dh v).ofReal_comp.mul (f.hasDerivAt v)).deriv)
    rw [d1] ; convert (l5.add l7) using 1 <;> simp [h] ; ring_nf

  obtain ⟨c1, mg'⟩ := (g : CS 2 ℝ).deriv.bounded ; obtain ⟨c2, mg''⟩ := (g : CS 2 ℝ).deriv.deriv.bounded
  let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖

  have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
    apply eventually_of_forall ; intro R ; apply Continuous.aestronglyMeasurable ; fun_prop

  have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
    filter_upwards [eventually_ge_atTop 1] with R hR
    apply eventually_of_forall ; intro v
    have e1 : 0 ≤ R := by linarith
    have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le (by linarith) (by simpa using hR)
    have e3 : R ≠ 0 := by linarith
    have hc1 : |G' R v| ≤ c1 := by
      simp [G', G, CS.deriv_scale, abs_mul, abs_inv, abs_eq_self.mpr e1] ; simp [CS.scale, CD.scale, funscale, e3]
      simpa using mul_le_mul e2 (mg' _) (norm_nonneg _) zero_le_one
    have hc2 : |G'' R v| ≤ c2 := by
      simp [G'', G', G, CS.deriv_scale, CS.deriv_smul, abs_mul, abs_inv, abs_eq_self.mpr e1]
      convert_to _ ≤ 1 * (1 * c2) ; simp
      gcongr ; simp [CS.scale, CD.scale, e3, funscale] ; apply mg''
    simp only [F, bound, norm_norm] ; refine (norm_add_le _ _).trans ?_ ; apply add_le_add
    · apply (norm_add_le _ _).trans ; simp ; gcongr
    · suffices hh1 : |h R v| ≤ 1 by simpa using mul_le_mul hh1 le_rfl (by simp) zero_le_one
      simp [h, G, e3, CS.scale, CD.scale, funscale] ; rw [abs_le] ; constructor <;>
      linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]

  have e3 : Integrable bound volume := by refine (Integrable.add ?_ ?_).add ?_ <;> fun_prop

  have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
    apply eventually_of_forall ; intro v
    have vR : Tendsto (fun R : ℝ => R⁻¹ * v) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero.mul_const v
    have evg' : (g : CS 2 ℝ).deriv =ᶠ[𝓝 0] 0 := by convert ← g.zero.deriv ; exact deriv_const' _
    have evg'' : (g : CS 2 ℝ).deriv.deriv =ᶠ[𝓝 0] 0 := by convert ← evg'.deriv ; exact deriv_const' _
    refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
    · apply tendsto_nhds_of_eventually_eq
      filter_upwards [vR.eventually evg'', eventually_ne_atTop 0] with R hR hR'
      simp [G'', G', G, CS.deriv_scale, CS.deriv_smul] ; simpa [CS.scale, CD.scale, hR', funscale] using .inl hR
    · apply tendsto_nhds_of_eventually_eq ; filter_upwards [vR.eventually evg'] with R hR
      simpa [G', G] using .inl (.inr hR)
    · simpa [h] using ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds

  simpa using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4
