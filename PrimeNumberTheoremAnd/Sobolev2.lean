import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

set_option maxHeartbeats 20000000

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators Set

attribute [fun_prop] Integrable Integrable.norm Integrable.const_mul Integrable.add Integrable.sub
attribute [fun_prop] AEStronglyMeasurable Continuous.aestronglyMeasurable
attribute [fun_prop] HasCompactSupport HasCompactSupport.smul_right HasCompactSupport.smul_right HasCompactSupport.mul_left

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

def CD (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Subspace ℝ (ℝ → E) where
  carrier := {f | ContDiff ℝ n f}
  zero_mem' := by change ContDiff ℝ (↑n) (fun _ => 0) ; apply contDiff_const
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := hf.const_smul c

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

@[fun_prop] nonrec lemma HasCompactSupport.iteratedDeriv {f : ℝ → E} (hf : HasCompactSupport f) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa [iteratedDeriv_succ] using ih.deriv

@[simp] lemma iteratedDeriv_zero_fun : iteratedDeriv n (0 : ℝ → E) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iteratedDeriv_succ, ih] ; apply deriv_const'

end lemmas

namespace CD

variable {f : CD n E} {R x v : ℝ}

instance : CoeFun (CD n E) (fun _ => ℝ → E) where coe f := f.1

instance : Coe (CD n ℝ) (CD n ℂ) where coe f := ⟨ofReal' ∘ f, contDiff_ofReal.of_le le_top |>.comp f.2⟩

def of_le (f : CD n E) {m : ℕ} (hm : m ≤ n) : CD m E := ⟨f, f.2.of_le (by simp [hm])⟩

def of_succ (f : CD (n + 1) E) : CD n E := ⟨f, f.2.of_succ⟩

instance : Coe (CD (n + 1) E) (CD n E) where coe f := of_succ f

@[continuity, fun_prop] lemma continuous (f : CD n E) : Continuous f := f.2.continuous

noncomputable nonrec def deriv (f : CD (n + 1) E) : CD n E := ⟨deriv f, (contDiff_succ_iff_deriv.mp f.2).2⟩

lemma hasDerivAt (f : CD (n + 1) E) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  (f.2.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CD (n + 1) E} {x : ℝ} : deriv f x = _root_.deriv f x := rfl

lemma deriv_const_smul {f : CD (n + 1) E} : deriv (R • f) = R • deriv f := by
  ext x ; exact (hasDerivAt f x |>.const_smul R).deriv

noncomputable def scale (g : CD n E) (R : ℝ) : CD n E := by
  by_cases R = 0
  · exact ⟨0, contDiff_const⟩
  · exact ⟨funscale g R, g.2.comp (contDiff_const.smul contDiff_id)⟩

lemma deriv_scale {f : CD (n + 1) E} : deriv (scale f R) = R⁻¹ • scale (deriv f) R := by
  ext v ; by_cases hR : R = 0 <;> simp [hR, scale]
  · simp [deriv] ; exact deriv_const _ _
  · exact ((hasDerivAt f (R⁻¹ • v)).scomp v (by simpa using (hasDerivAt_id v).const_smul R⁻¹)).deriv

@[simp] lemma deriv_scale' {f : CD (n + 1) E} : deriv (scale f R) v = R⁻¹ • deriv f (R⁻¹ • v) := by
  rw [deriv_scale] ; by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CD (n + 1) E) (R x : ℝ) :
    HasDerivAt (scale f R) (R⁻¹ • deriv f (R⁻¹ • x)) x := by
  simpa using hasDerivAt (scale f R) x

lemma tendsto_scale (f : CD n E) (x : ℝ) : Tendsto (fun R => scale f R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.2.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

def mul (f g : CD n 𝕜) : CD n 𝕜 := ⟨f * g, f.2.mul g.2⟩

instance : Mul (CD n 𝕜) where mul := mul

nonrec lemma deriv_mul (f g : CD (n + 1) 𝕜) : deriv (f * g) = deriv f * of_succ g + of_succ f * deriv g := by
  ext t
  have l1 : DifferentiableAt ℝ f t := (f.2.differentiable (by simp)).differentiableAt
  have l2 : DifferentiableAt ℝ g t := (g.2.differentiable (by simp)).differentiableAt
  exact deriv_mul l1 l2

def smul (f : CD n ℝ) (g : CD n E) : CD n E := ⟨fun t => f t • g t, f.2.smul g.2⟩

instance : SMul (CD n ℝ) (CD n E) where smul := smul

nonrec lemma deriv_smul (f : CD (n + 1) ℝ) (g : CD (n + 1) E) :
    deriv (f • g) = of_succ f • deriv g + deriv f • of_succ g := by
  ext t
  have l1 : DifferentiableAt ℝ f t := (f.2.differentiable (by simp)).differentiableAt
  have l2 : DifferentiableAt ℝ g t := (g.2.differentiable (by simp)).differentiableAt
  exact deriv_smul l1 l2

noncomputable nonrec def iteratedDeriv (k : ℕ) (f : CD (n + k) E) : CD n E := by
  refine ⟨iteratedDeriv k f, ?_⟩
  simpa [iteratedDeriv_eq_iterate] using f.2.iterate_deriv' n k

noncomputable def iteratedDeriv_of_le {n : ℕ} ⦃k : ℕ⦄ (hk : k ≤ n) (f : CD n E) : CD (n - k) E := by
  refine ⟨_root_.iteratedDeriv k f, ?_⟩
  have := Nat.le.dest hk ; simp_rw [add_comm k] at this ; obtain ⟨l, rfl⟩ := this ; simp
  simpa [iteratedDeriv_eq_iterate] using f.2.iterate_deriv' l k

@[simp] lemma iteratedDeriv_of_le_zero (hk : k ≤ n) : iteratedDeriv_of_le hk (0 : CD n E) = 0 := by
  simp [iteratedDeriv_of_le]

@[simp] lemma iteratedDeriv_of_le_add (hk : k ≤ n) (f g : CD n E) :
    iteratedDeriv_of_le hk (f + g) = iteratedDeriv_of_le hk f + iteratedDeriv_of_le hk g := by
  ext x ; simp [iteratedDeriv_of_le, iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDeriv_add_apply] ; rfl
  · apply f.2.of_le ; simp [hk]
  · apply g.2.of_le ; simp [hk]

@[simp] lemma iteratedDeriv_of_le_neg (hk : k ≤ n) (f : CD n E) :
    iteratedDeriv_of_le hk (-f) = -iteratedDeriv_of_le hk f := by
  ext x ; simp [iteratedDeriv_of_le] ; apply iteratedDeriv_neg

@[simp] lemma iteratedDeriv_of_le_smul (hk : k ≤ n) (c : ℝ) (f : CD n E) :
    iteratedDeriv_of_le hk (c • f) = c • iteratedDeriv_of_le hk f := by
  ext x ; simp [iteratedDeriv_of_le, iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDeriv_const_smul_apply] ; rfl
  apply f.2.of_le ; simp [hk]

nonrec lemma iteratedDeriv_succ {k : ℕ} {f : CD (n + (k + 1)) E} :
    iteratedDeriv (k + 1) f = iteratedDeriv k (deriv f) := by
  simp [iteratedDeriv, iteratedDeriv_succ'] ; rfl

nonrec lemma deriv_add (f g : CD (n + 1) E) : deriv (f + g) = deriv f + deriv g := by
  ext x
  apply deriv_add
  · exact (f.2.differentiable (by simp)).differentiableAt
  · exact (g.2.differentiable (by simp)).differentiableAt

lemma iteratedDeriv_add {k : ℕ} {f g : CD (n + k) E} :
    iteratedDeriv k (f + g) = iteratedDeriv k f + iteratedDeriv k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp_rw [iteratedDeriv_succ, deriv_add, ih]

lemma iteratedDeriv_add' {k : ℕ} {f g : CD (n + k) E} {x : ℝ} :
    iteratedDeriv k (f + g) x = iteratedDeriv k f x + iteratedDeriv k g x := by
  rw [iteratedDeriv_add] ; rfl

end CD

def CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Subspace ℝ (CD n E) where
  carrier := {f | HasCompactSupport f}
  zero_mem' := by change HasCompactSupport (fun _ => 0) ; simp [HasCompactSupport, tsupport]
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := hf.smul_left

namespace CS

variable {f : CS n E} {R x v : ℝ}

-- lemma ext_CD {f g : CS n E} (h : f.toCD = g.toCD) : f = g := by
--   cases f ; cases g ; simp ; exact h

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe f := f.1

instance : Coe (CS n E) (CD n E) where coe f := f.1

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨f, f.2.comp_left (g := ofReal') rfl⟩

nonrec def of_le (f : CS n E) {m : ℕ} (hm : m ≤ n) : CS m E := ⟨CD.of_le f hm, by exact f.2⟩

nonrec def of_succ (f : CS (n + 1) E) : CS n E := of_le f (by simp)

instance : Coe (CS (n + 1) E) (CS n E) where coe := of_succ

noncomputable nonrec def deriv (f : CS (n + 1) E) : CS n E := ⟨CD.deriv f, f.2.deriv⟩

nonrec lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (deriv f x) x := CD.hasDerivAt _ _

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : deriv f x = _root_.deriv f x := rfl

lemma deriv_smul {f : CS (n + 1) E} : deriv (R • f) = R • deriv f := by
  ext x ; exact (hasDerivAt f x |>.const_smul R).deriv

noncomputable nonrec def scale (g : CS n E) (R : ℝ) : CS n E := by
  refine ⟨CD.scale g R, ?_⟩
  by_cases h : R = 0 <;> simp [CD.scale, h]
  · simp [CS, HasCompactSupport, tsupport]
  · exact g.2.comp_smul (inv_ne_zero h)

nonrec lemma deriv_scale {f : CS (n + 1) E} : deriv (scale f R) = R⁻¹ • scale (deriv f) R := by
  ext1 ; exact CD.deriv_scale

nonrec lemma of_succ_scale {f : CS (n + 1) E} : scale (of_succ f) R = of_succ (scale f R) := by
  ext ; by_cases hR : R = 0 <;> simp [scale, CD.scale, of_succ, of_le, CD.of_le, hR]

@[simp] lemma deriv_scale' {f : CS (n + 1) E} : deriv (scale f R) v = R⁻¹ • deriv f (R⁻¹ • v) := CD.deriv_scale'

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (scale f R) (R⁻¹ • deriv f (R⁻¹ • x)) x := CD.hasDerivAt_scale _ _ _

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => scale f R x) atTop (𝓝 (f 0)) := CD.tendsto_scale _ _

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ := (continuous_norm.comp f.1.2.continuous).exists_forall_ge_of_hasCompactSupport f.2.norm
  refine ⟨_, hx⟩

@[simp] lemma bounded' : BddAbove (range fun v ↦ ‖f v‖) :=
  (f.2.norm.isCompact_range (by fun_prop)).bddAbove

lemma bounded'_of_le (hk : k ≤ n) : BddAbove (range fun v ↦ ‖iteratedDeriv k f v‖) := by
  apply IsCompact.bddAbove
  apply f.2.iteratedDeriv.norm.isCompact_range
  exact f.1.2.continuous_iteratedDeriv k (by simp [hk]) |>.norm

lemma integrable (f : CS n E) : Integrable f := f.1.2.continuous.integrable_of_hasCompactSupport f.2

lemma integrable_iteratedDeriv {n : ℕ} (f : CS n E) : Integrable (iteratedDeriv n f) := by
  induction n with
  | zero => exact integrable f
  | succ n ih => simpa [iteratedDeriv_succ'] using ih (deriv f)

lemma integrable_iteratedDeriv_of_le {n : ℕ} (f : CS n E) ⦃k : ℕ⦄ (hk : k ≤ n) : Integrable (iteratedDeriv k f) := by
  obtain ⟨m, rfl⟩ := Nat.le.dest hk ; exact integrable_iteratedDeriv (of_le f hk)

noncomputable def norm (f : CS n E) : ℝ :=
  Finset.sup' (s := Finset.range (n + 1)) (by simp) (fun k => ⨆ v, ‖iteratedDeriv k f v‖)

noncomputable instance : Norm (CS n E) where norm := norm

@[simp] nonrec lemma norm_nonneg : 0 ≤ ‖f‖ := by
  simp [Norm.norm, norm] ; use 0 ; simp
  apply (norm_nonneg (f 0)).trans
  apply le_ciSup (f := fun x => ‖f x‖) bounded'

lemma le_norm (f : CS n E) (x : ℝ) : ‖f x‖ ≤ ‖f‖ := by
  apply (le_ciSup bounded' x).trans
  exact Finset.le_sup' (b := 0) (fun k => ⨆ v, ‖iteratedDeriv k f v‖) (by simp)

lemma le_norm_of_le (f : CS n E) (hk : k ≤ n) (x : ℝ) : ‖iteratedDeriv k f x‖ ≤ ‖f‖ := by
  apply (le_ciSup (bounded'_of_le hk) x).trans
  refine Finset.le_sup' (b := k) (fun k => ⨆ v, ‖iteratedDeriv k f v‖) (by simp ; omega)

lemma norm_of_succ (f : CS (n + 1) E) : ‖of_succ f‖ ≤ ‖f‖ := by
  simp_rw [Norm.norm, norm] ; apply Finset.sup'_mono ; simp

lemma norm_succ {f : CS (n + 1) E} : ‖f‖ = (⨆ v, ‖f v‖) ⊔ ‖deriv f‖ := by
  simp_rw [Norm.norm, norm, deriv, CD.deriv, ← iteratedDeriv_succ']
  let s : ℕ ↪ ℕ := ⟨fun n => n + 1, Nat.succ_injective⟩
  have l1 : _ = Finset.sup' (.range (n + 1)) _ ((fun k ↦ ⨆ v, ‖iteratedDeriv (k + 1) f v‖)) :=
    @Finset.sup'_map ℝ ℕ ℕ _ (.range (n + 1)) s (fun k => ⨆ v, ‖iteratedDeriv k f v‖) (by simp)
  have l2 : Finset.map s (Finset.range (n + 1)) = Finset.Ico 1 (n + 2) := by
    ext i ; simp [s] ; constructor
    · rintro ⟨a, h1, h2⟩ ; omega
    · rintro ⟨h1, h2⟩ ; use i - 1 ; omega
  have l3 : insert 0 (Finset.Ico 1 (n + 2)) = Finset.range (n + 2) := by ext i ; simp ; omega
  simp [← l1, l2, ← l3]

lemma norm_deriv (f : CS (n + 1) E) : ‖deriv f‖ ≤ ‖f‖ := by
  simp only [norm_succ, le_sup_right]

nonrec lemma norm_smul (c : ℝ) (f : CS n E) : ‖c • f‖ = |c| * ‖f‖ := by
  simp [Norm.norm, norm]
  have l1 (x y : ℝ) : |c| * (x ⊔ y) = |c| * x ⊔ |c| * y := by
    apply mul_max_of_nonneg ; apply abs_nonneg
  have := @Finset.comp_sup'_eq_sup'_comp ℝ ℕ ℝ _ _ (.range (n + 1)) (by simp)
    (fun k => ⨆ v, ‖iteratedDeriv k f v‖) (fun x => |c| * x) l1 ; simp at this ; rw [this]
  apply Finset.sup'_congr ; rfl ; intro k hk ; simp at hk
  rw [Real.mul_iSup_of_nonneg (abs_nonneg _)] ; congr ; ext x
  simp [iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDeriv_const_smul_apply (f.1.2.of_le (by simp ; omega))]
  simp [norm_smul]

lemma norm_scale (R : ℝ) (hR : 1 ≤ R) (f : CS n E) : ‖scale f R‖ ≤ ‖f‖ := by
  simp_rw [Norm.norm, norm]
  apply Finset.sup'_le ; intro k hk ; apply Finset.le_sup'_of_le _ hk ; simp at hk
  apply ciSup_le ; intro x ; apply le_ciSup_of_le (bounded'_of_le (by omega)) (R⁻¹ * x)
  have l1 : R ≠ 0 := by positivity
  have l2 : ContDiff ℝ k f := f.1.2.of_le (by simp ; omega)
  simp [scale, CD.scale, l1] ; unfold funscale ; simp [iteratedDeriv_const_smul l2, _root_.norm_smul]
  convert_to _ ≤ 1 * ‖iteratedDeriv k (↑↑f) (R⁻¹ * x)‖ ; simp
  gcongr ; apply inv_le_one ; apply one_le_pow_of_one_le
  rw [abs_eq_self.mpr (by positivity)] ; exact hR

instance : SMul (CS n ℝ) (CD n E) := sorry

end CS

structure trunc where
  toFun : CS 2 ℝ
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ ⇑toFun
  h4 : ⇑toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := toFun

instance : Coe trunc (CD 2 ℝ) where coe f := f.1

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 := (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

def W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Subspace ℝ (CD n E) where
  carrier := {f | ∀ ⦃k : ℕ⦄ (hk : k ≤ n), Integrable (CD.iteratedDeriv_of_le hk f)}
  zero_mem' k hk := by simp ; exact integrable_zero ℝ E _
  add_mem' {f g} hf hg k hk := by simpa using (hf hk).add (hg hk)
  smul_mem' c f hf k hk := by simpa using hf hk |>.smul c

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe f := f

instance : Coe (W1 n E) (CD n E) where coe f := f

@[fun_prop] lemma integrable' (f : W1 n E) : Integrable f := by
  exact f.prop (k := 0) (by simp)

@[fun_prop, continuity] lemma continuous (f : W1 n E) : Continuous f := f.1.2.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.1.2.differentiable (by simp)

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

lemma iteratedDeriv_add {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f + g) = iteratedDeriv n f + iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f + g) = deriv f + deriv g := by
      ext x ; apply deriv_add
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  val := CD.deriv f
  property k hk := by
    simpa [CD.iteratedDeriv_of_le, CD.deriv, ← iteratedDeriv_succ'] using
      f.2 (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (deriv f x) x := CD.hasDerivAt _ _

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using ih (f := SchwartzMap.derivCLM ℝ f)

def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ := by
  refine ⟨⟨f, f.smooth n⟩, fun _ _ => integrable_iteratedDeriv_Schwarz⟩

instance : Coe (CS n E) (W1 n E) where
  coe f := ⟨f, CS.integrable_iteratedDeriv_of_le f⟩

def smul (g : CS n ℝ) (f : W1 n E) : W1 n E := by
  refine ⟨CD.smul g f, ?_⟩
  intro k hk
  obtain ⟨l, rfl⟩ : ∃ l, l + k = n := by simpa [add_comm k] using Nat.le.dest hk
  apply (CD.continuous _).integrable_of_hasCompactSupport
  exact g.2.smul_right.iteratedDeriv

instance : SMul (CS n ℝ) (W1 n E) where smul := smul

noncomputable def L1_norm (f : ℝ → E) : ℝ := ∫ v, ‖f v‖

lemma L1_norm_add {f g : ℝ → E} (hf : Integrable f) (hg : Integrable g) :
    L1_norm (f + g) ≤ L1_norm f + L1_norm g := by
  rw [L1_norm, L1_norm, L1_norm, ← integral_add' hf.norm hg.norm]
  apply integral_mono (by fun_prop) (by fun_prop) ; intro t ; simp ; apply norm_add_le

lemma L1_norm_sub {f g : ℝ → E} (hf : Integrable f) (hg : Integrable g) :
    L1_norm (f - g) ≤ L1_norm f + L1_norm g := by
  rw [L1_norm, L1_norm, L1_norm, ← integral_add' hf.norm hg.norm]
  apply integral_mono (by fun_prop) (by fun_prop) ; intro t ; simp ; apply norm_sub_le

noncomputable def norm1 (f : W1 n E) : ℝ := L1_norm f

lemma norm1_nonneg (f : W1 n E) : 0 ≤ norm1 f := by
  rw [norm1, L1_norm] ; positivity

noncomputable def norm (n : ℕ) (f : ℝ → E) : ℝ :=
  ∑ k in Finset.range (n + 1), L1_norm (iteratedDeriv k f)

noncomputable instance : Norm (W1 n E) where norm f := norm n f

@[simp] lemma norm_of_zero (f : W1 0 E) : ‖f‖ = L1_norm f := by simp [Norm.norm, norm]

@[simp] lemma norm_nonneg {f : W1 n E} : 0 ≤ ‖f‖ := by
  simp [Norm.norm, norm, L1_norm] ; positivity

lemma norm_succ (f : W1 (n + 1) E) : ‖f‖ = norm1 f + ‖deriv f‖ := by
  simp [Norm.norm, norm, norm1, deriv, CD.deriv, ← iteratedDeriv_succ', Finset.sum_range_succ' _ (n + 1)] ; ring

lemma integral_norm_le_norm (f : W1 n E) : norm1 f ≤ ‖f‖ := by
  have l1 i (_ : i ∈ Finset.range (n + 1)) : 0 ≤ ∫ (v : ℝ), ‖iteratedDeriv i f v‖ := by positivity
  have l2 : 0 ∈ Finset.range (n + 1) := by simp
  exact Finset.single_le_sum l1 l2

lemma norm_deriv (f : W1 (n + 1) E) : ‖deriv f‖ ≤ ‖f‖ := by
  rw [norm_succ] ; linarith [norm1_nonneg f]

lemma norm_mul0 (g : CS n ℝ) (f : W1 n E) : norm1 (g • f) ≤ ‖g‖ * norm1 f := by
  convert_to ∫ v, ‖g v • f v‖ ≤ ‖g‖ * (∫ v, ‖f v‖) using 0
  rw [← integral_mul_left]
  apply integral_mono
  · exact W1.integrable' (g • f) |>.norm
  · fun_prop
  · intro v ; simp [norm_smul] ; gcongr ; exact CS.le_norm g v

def of_succ (f : W1 (n + 1) E) : W1 n E := ⟨f, fun k hk => f.2 (by omega)⟩

instance : Coe (W1 (n + 1) E) (W1 n E) where coe := of_succ

lemma norm_of_succ (f : W1 (n + 1) E) : ‖of_succ f‖ ≤ ‖f‖ := by
  simp_rw [Norm.norm, norm, L1_norm] ; apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
  rintro i - - ; positivity

nonrec lemma deriv_sub (f g : W1 (n + 1) E) : deriv (f - g) = deriv f - deriv g := by
  ext x ; apply deriv_sub
  · exact f.1.2.differentiable (by simp) |>.differentiableAt
  · exact g.1.2.differentiable (by simp) |>.differentiableAt

lemma deriv_smul {g : CS (n + 1) ℝ} {f : W1 (n + 1) E} :
    deriv (g • f) = CS.of_succ g • deriv f + CS.deriv g • of_succ f := by
  ext x ; apply _root_.deriv_smul
  · exact g.1.2.differentiable (by simp) |>.differentiableAt
  · exact f.1.2.differentiable (by simp) |>.differentiableAt

lemma norm_add_le {f g : W1 n E} : ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
  simp [Norm.norm, norm, ← Finset.sum_add_distrib] ; apply Finset.sum_le_sum ; intro k hk
  have lk : k ≤ n := by simp at hk ; omega
  have l1 : ContDiff ℝ k f := by apply f.1.2.of_le ; simp [lk]
  have l2 : ContDiff ℝ k g := by apply g.1.2.of_le ; simp [lk]
  have l3 : Integrable (iteratedDeriv k f) := by apply f.2 lk
  have l4 : Integrable (iteratedDeriv k g) := by apply g.2 lk
  change L1_norm (iteratedDeriv k (⇑f + ⇑g)) ≤ _
  rw [iteratedDeriv_add l1 l2] ; apply L1_norm_add l3 l4

lemma norm_sub_le {f g : W1 n E} : ‖f - g‖ ≤ ‖f‖ + ‖g‖ := by
  simp [Norm.norm, norm, ← Finset.sum_add_distrib] ; apply Finset.sum_le_sum ; intro k hk
  have lk : k ≤ n := by simp at hk ; omega
  have l1 : ContDiff ℝ k f := by apply f.1.2.of_le ; simp [lk]
  have l2 : ContDiff ℝ k g := by apply g.1.2.of_le ; simp [lk]
  have l3 : Integrable (iteratedDeriv k f) := by apply f.2 lk
  have l4 : Integrable (iteratedDeriv k g) := by apply g.2 lk
  change L1_norm (iteratedDeriv k (⇑f - ⇑g)) ≤ _
  rw [iteratedDeriv_sub l1 l2] ; apply L1_norm_sub l3 l4

theorem norm_mul (g : CS n ℝ) (f : W1 n E) : ‖g • f‖ ≤ (2 ^ (n + 1) - 1) * (‖g‖ * ‖f‖) := by
  induction n with
  | zero =>
    conv => enter [2, 1] ; norm_num
    simp only [Norm.norm, norm, Nat.add_one, Finset.range_one, Finset.sum_singleton, iteratedDeriv_zero, one_mul]
    exact norm_mul0 g f
  | succ n ih =>
    have l1 : (0 : ℝ) ≤ 2 ^ (n + 1) - 1 := by simp ; norm_cast ; apply Nat.one_le_pow'
    have key1 : norm1 (g • f) ≤ ‖g‖ * ‖f‖ := by
      apply norm_mul0 g f |>.trans
      have := integral_norm_le_norm f
      gcongr ; apply CS.norm_nonneg
    have key2 : ‖CS.of_succ g • deriv f‖ ≤ (2 ^ (n + 1) - 1) * (‖g‖ * ‖f‖) := by
      apply ih (CS.of_succ g) (deriv f) |>.trans
      have := norm_deriv f
      have := CS.norm_of_succ g
      gcongr ; apply norm_nonneg ; apply CS.norm_nonneg
    have key3 : ‖CS.deriv g • of_succ f‖ ≤ (2 ^ (n + 1) - 1) * (‖g‖ * ‖f‖) := by
      apply ih (CS.deriv g) (of_succ f) |>.trans
      have := norm_of_succ f
      have := CS.norm_deriv g
      gcongr ; apply norm_nonneg ; apply CS.norm_nonneg
    have key4 : ‖deriv (g • f)‖ ≤ (2 ^ (n + 2) - 2) * (‖g‖ * ‖f‖) := by
      rw [deriv_smul] ; apply norm_add_le.trans
      convert add_le_add key2 key3 using 1 ; simp [pow_succ] ; ring
    rw [norm_succ] ; convert add_le_add key1 key4 using 1 ; simp [pow_succ] ; ring

lemma approx0 (f : W1 n E) (g : CS n ℝ) (hg : g 0 = 1) :
    Tendsto (fun R ↦ norm1 (f - CS.scale g R • f)) atTop (𝓝 0) := by

  let F R x := ‖(f - CS.scale g R • f) x‖
  let bound x := (1 + ‖g‖) * ‖f x‖
  have l1 : ∀ᶠ (R : ℝ) in atTop, AEStronglyMeasurable (F R) volume := by
    apply eventually_of_forall ; intro R
    apply Continuous.aestronglyMeasurable
    fun_prop
  have l2 : ∀ᶠ R in atTop, ∀ᵐ x, ‖F R x‖ ≤ bound x := by
    filter_upwards [eventually_ne_atTop 0] with R hR
    apply eventually_of_forall ; intro x
    convert_to ‖f x - (CS.scale g R • f) x‖ ≤ ‖f x‖ + ‖g‖ * ‖f x‖
    · simp only [F, norm_norm] ; congr
    · simp [bound] ; ring
    apply (_root_.norm_sub_le _ _).trans ; gcongr
    change ‖CS.scale g R x • f x‖ ≤ ‖g‖ * ‖f x‖ ; simp [norm_smul] ; gcongr
    simpa [CS.scale, CD.scale, hR, funscale] using CS.le_norm g (R⁻¹ * x)
  have l3 : Integrable bound volume := (W1.integrable' f).norm.const_mul _
  have l4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
    apply eventually_of_forall ; intro x
    simpa [hg] using (((CS.tendsto_scale g x).smul_const (f x)).const_sub (f x)).norm
  haveI : AddGroup (W1 n E) := AddCommGroup.toAddGroup
  simpa using tendsto_integral_filter_of_dominated_convergence bound l1 l2 l3 l4

theorem W1_approximation (f : W1 n E) (g : CS n ℝ) (hg : g 0 = 1) :
    Tendsto (fun R => ‖f - CS.scale g R • f‖) atTop (𝓝 0) := by

  induction n with
  | zero =>
    convert approx0 f g hg
    ext f ; simp only [Norm.norm, norm, Nat.zero_eq, zero_add, Finset.range_one,
      Finset.sum_singleton, iteratedDeriv_zero] ; rfl
  | succ n ih =>
    simp_rw [norm_succ] ; apply ZeroAtFilter.add (approx0 f g hg)
    simp_rw [deriv_sub, deriv_smul]
    convert_to ZeroAtFilter atTop fun R ↦
        ‖(deriv f - CS.of_succ (CS.scale g R) • deriv f) - CS.deriv (CS.scale g R) • of_succ f‖
        using 1
    · ext R ; congr 1 ; ext x ; simp [sub_sub]
    simp_rw [← CS.of_succ_scale, CS.deriv_scale, ZeroAtFilter]
    have key1 := ih (deriv f) (CS.of_succ g) hg
    rw [Metric.tendsto_nhds] at key1 ⊢ ; intro ε hε
    specialize key1 (ε / 2) (by positivity)
    have key2 : ∀ᶠ R in atTop, (2 ^ (n + 1) - 1) * R⁻¹ * ‖g‖ * ‖f‖ < ε / 2 := by
      have := tendsto_inv_atTop_zero (𝕜 := ℝ) |>.const_mul (2 ^ (n + 1) - 1) |>.mul_const ‖g‖ |>.mul_const ‖f‖
      simp at this ; apply eventually_lt_of_tendsto_lt _ this ; positivity
    filter_upwards [key1, key2, eventually_ge_atTop 1] with R key1 key2 hR
    haveI : AddGroup (W1 n E) := AddCommGroup.toAddGroup
    simp only [dist_zero_right, Real.norm_eq_abs] at key1 ⊢
    rw [abs_eq_self.mpr (W1.norm_nonneg)] at key1 ⊢
    apply norm_sub_le.trans_lt
    convert_to _ < ε / 2 + ε / 2 ; ring
    gcongr
    apply norm_mul _ _ |>.trans_lt
    refine LE.le.trans_lt ?_ key2
    have : (0 : ℝ) ≤ 2 ^ (n + 1) - 1 := by simp ; norm_cast ; apply Nat.one_le_pow'
    convert_to (2 ^ (n + 1) - 1) * ‖R⁻¹ • CS.scale (CS.deriv g) R‖ * ‖of_succ f‖ ≤
      (2 ^ (n + 1) - 1) * (R⁻¹ * ‖g‖) * ‖f‖ ; ring ; ring
    gcongr ; simp ; apply mul_nonneg ; linarith ; apply mul_nonneg ; positivity ; simp
    · simp [CS.norm_smul] ; gcongr ; simp ; rw [abs_eq_self.mpr] ; positivity
      apply CS.norm_scale R hR (CS.deriv g) |>.trans
      apply CS.norm_deriv
    · apply norm_of_succ

#print axioms W1_approximation

end W1

abbrev W21 : Type _ := W1 2 ℂ

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

def mul_CSC_W21 (g : CS 2 ℂ) (f : W21) : CS 2 ℂ := ⟨⟨g * f, g.1.2.mul f.1.2⟩, g.2.mul_right⟩

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where hMul := mul_CSC_W21

noncomputable instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where
  hMul g f := by
    refine ⟨g * f, ?_⟩
    apply HasCompactSupport.mul_right
    exact @HasCompactSupport.comp_left ℝ ℝ ℂ _ _ _ ofReal' g g.2 rfl
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
    Tendsto (fun R => ‖f - CS.scale (g : CS 2 ℝ) R • f‖) atTop (𝓝 0) := by

  -- Setup
  let G R : CS 2 ℝ := CS.scale g R ; let h R v := 1 - G R v
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl

  -- Take care of the first piece
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  have piece_1 : Tendsto (fun R ↦ ∫ v, ‖h R v * f v‖) atTop (𝓝 0) := by
    apply approx_aux2 (W1.integrable' f) g.le_one g.nonneg (CD.continuous (g : CD 2 ℝ)) g.zero_at |>.congr'
    filter_upwards [eventually_ne_atTop 0] with R hR ; simp [h, G, CS.scale, CD.scale, hR]
  refine piece_1.add (Tendsto.const_mul _ ?_) ; clear piece_1

  -- Definitions
  let f' := (W1.deriv f) ; let f'' := W1.deriv f'
  let G' R := CS.deriv (G R) ; let G'' R := CS.deriv (G' R)
  let F R v := ‖- G'' R v * f v + 2 * -G' R v * f' v + h R v * f'' v‖

  -- Proof
  convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
  · ext R ; congr ; ext v ; congr ; apply HasDerivAt.deriv
    have dh v : HasDerivAt (h R) (-G' R v) v := by
      simpa [G', G] using CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1
    have l5 := (CS.hasDerivAt (G' R) v).ofReal_comp.neg.mul (W1.hasDerivAt f v)
    have l7 := (dh v).ofReal_comp.mul (W1.hasDerivAt f' v)
    have d1 : deriv _ = _ := funext (fun v => ((dh v).ofReal_comp.mul (W1.hasDerivAt f v)).deriv)
    rw [d1] ; convert (l5.add l7) using 1 <;> simp [h] ; ring_nf

  obtain ⟨c1, mg'⟩ := CS.bounded (f := CS.deriv (g : CS 2 ℝ))
  obtain ⟨c2, mg''⟩ := CS.bounded (f := CS.deriv <| CS.deriv (g : CS 2 ℝ))
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
    have evg' : CS.deriv (g : CS 2 ℝ) =ᶠ[𝓝 0] 0 := by convert ← g.zero.deriv ; exact deriv_const' _
    have evg'' : CS.deriv (CS.deriv (g : CS 2 ℝ)) =ᶠ[𝓝 0] 0 := by convert ← evg'.deriv ; exact deriv_const' _
    refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
    · apply tendsto_nhds_of_eventually_eq
      filter_upwards [vR.eventually evg'', eventually_ne_atTop 0] with R hR hR'
      simp [G'', G', G, CS.deriv_scale, CS.deriv_smul] ; simpa [CS.scale, CD.scale, hR', funscale] using .inl hR
    · apply tendsto_nhds_of_eventually_eq ; filter_upwards [vR.eventually evg'] with R hR
      simpa [G', G] using .inl (.inr hR)
    · simpa [h] using ((CS.tendsto_scale (g : CS 2 ℝ) v).const_sub 1).ofReal.mul tendsto_const_nhds

  simpa using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

#print axioms W21_approximation
