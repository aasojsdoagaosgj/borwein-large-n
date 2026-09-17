import Borwein.IntervalLocalization

namespace Borwein.AbelRadialBound
noncomputable section
open scoped BigOperators

theorem abel_identity (f : ℕ → ℂ) (t : ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, t^i*f i) =
      t^n*(∑ i ∈ Finset.range n, f i)+
        (1-t)*(∑ i ∈ Finset.range n, t^i*(∑ j ∈ Finset.range (i+1), f j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    rw [Finset.sum_range_succ (fun i => f i),
      Finset.sum_range_succ (fun i => t^i*(∑ j ∈ Finset.range (i+1), f j)),
      Finset.sum_range_succ (fun i => f i),pow_succ]
    ring

theorem weight_identity (t : ℝ) (n : ℕ) :
    t^n+(1-t)*(∑ i ∈ Finset.range n, t^i) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,pow_succ]
    nlinarith

theorem radial_sum_bound (f : ℕ → ℂ) (t M : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) (hM : ∀ m ≤ n, ‖∑ i ∈ Finset.range m, f i‖ ≤ M) :
    ‖∑ i ∈ Finset.range n, (t:ℂ)^i*f i‖ ≤ M := by
  rw [abel_identity]
  have h0 := hM 0 (Nat.zero_le n)
  simp only [Finset.sum_range_zero,norm_zero] at h0
  have hfirst : ‖(t:ℂ)^n*(∑ i ∈ Finset.range n, f i)‖ ≤ t^n*M := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (hM n le_rfl) (pow_nonneg ht n)
  have hsum : ‖∑ i ∈ Finset.range n, (t:ℂ)^i*(∑ j ∈ Finset.range (i+1), f j)‖ ≤
      (∑ i ∈ Finset.range n, t^i)*M := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (hM (i+1) (by have h := Finset.mem_range.mp hi; omega))
      (pow_nonneg ht i)
  have hsecond : ‖(1-(t:ℂ))*(∑ i ∈ Finset.range n, (t:ℂ)^i*(∑ j ∈ Finset.range (i+1), f j))‖ ≤
      (1-t)*((∑ i ∈ Finset.range n, t^i)*M) := by
    rw [norm_mul,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
    exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr ht1)
  have h := (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  refine h.trans_eq ?_
  calc
    t^n*M+(1-t)*((∑ i ∈ Finset.range n, t^i)*M) =
        (t^n+(1-t)*(∑ i ∈ Finset.range n, t^i))*M := by ring
    _ = M := by rw [weight_identity,one_mul]

def block (z : ℂ) := z+z^2+z^3+z^4

theorem block_sum (n : ℕ) (z : ℂ) :
    (∑ i ∈ Finset.range n, (z^5)^i*block z) = FiniteFourierKernel.finiteSum n z := by
  rw [← Finset.sum_mul,FiniteFourierKernel.finiteSum_blocks]
  rfl

theorem unit_block_prefix_bound (n : ℕ) (u : ℝ)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖∑ i ∈ Finset.range n, (AngularKernel.circle u^5)^i*block (AngularKernel.circle u)‖ ≤
      RadialKernelProfile.profile u := by
  rw [block_sum]
  have h := RadialKernelProfile.exponential_finite_upper n 0 u (by norm_num) hu h5u
  simp at h
  linarith

theorem weighted_unit_blocks (n : ℕ) (ρ u : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖(∑ i ∈ Finset.range n, (((ρ:ℂ)*AngularKernel.circle u)^5)^i)*block (AngularKernel.circle u)‖ ≤
      RadialKernelProfile.profile u := by
  have h := radial_sum_bound (fun i => (AngularKernel.circle u^5)^i*block (AngularKernel.circle u))
    (ρ^5) (RadialKernelProfile.profile u) (pow_nonneg hρ _) (pow_le_one₀ hρ hρ1) n
    (fun m _ => unit_block_prefix_bound m u hu h5u)
  have he : (∑ i ∈ Finset.range n, ((ρ^5:ℝ):ℂ)^i*
      ((AngularKernel.circle u^5)^i*block (AngularKernel.circle u))) =
      (∑ i ∈ Finset.range n, (((ρ:ℂ)*AngularKernel.circle u)^5)^i)*block (AngularKernel.circle u) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_pow,Complex.ofReal_pow]
    ring
  rwa [he] at h

theorem radial_power_error (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (z : ℂ) (hz : ‖z‖ = 1) (r : ℕ) (hr : r ≤ 5) :
    ‖((ρ:ℂ)*z)^r-z^r‖ ≤ 1-ρ^5 := by
  have hp := pow_le_one₀ hρ hρ1 (n := r)
  have hp5 := pow_le_pow_of_le_one hρ hρ1 hr
  have he : ((ρ:ℂ)*z)^r-z^r = (((ρ^r-1:ℝ):ℂ))*z^r := by
    push_cast
    rw [mul_pow]
    ring
  rw [he,norm_mul,norm_pow,hz,one_pow,mul_one,Complex.norm_real,
    Real.norm_of_nonpos (sub_nonpos.mpr hp)]
  linarith

theorem block_radial_error (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (z : ℂ) (hz : ‖z‖ = 1) : ‖block ((ρ:ℂ)*z)-block z‖ ≤ 4*(1-ρ^5) := by
  have h1 := radial_power_error ρ hρ hρ1 z hz 1 (by norm_num)
  have h2 := radial_power_error ρ hρ hρ1 z hz 2 (by norm_num)
  have h3 := radial_power_error ρ hρ hρ1 z hz 3 (by norm_num)
  have h4 := radial_power_error ρ hρ hρ1 z hz 4 (by norm_num)
  have he : block ((ρ:ℂ)*z)-block z =
      ((((ρ:ℂ)*z)^1-z^1)+(((ρ:ℂ)*z)^2-z^2))+
      ((((ρ:ℂ)*z)^3-z^3)+(((ρ:ℂ)*z)^4-z^4)) := by unfold block; ring
  rw [he]
  calc
    _ ≤ (‖((ρ:ℂ)*z)^1-z^1‖+‖((ρ:ℂ)*z)^2-z^2‖)+
        (‖((ρ:ℂ)*z)^3-z^3‖+‖((ρ:ℂ)*z)^4-z^4‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ 4*(1-ρ^5) := by linarith

theorem geometric_norm_bound (n : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖∑ i ∈ Finset.range n, (((ρ:ℂ)*z)^5)^i‖ ≤ ∑ i ∈ Finset.range n, (ρ^5)^i := by
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_pow,norm_pow,norm_mul,Complex.norm_real,Real.norm_of_nonneg hρ,hz,mul_one]

theorem radial_block_sum_error (n : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(∑ i ∈ Finset.range n, (((ρ:ℂ)*z)^5)^i)*(block ((ρ:ℂ)*z)-block z)‖ ≤ 4 := by
  rw [norm_mul]
  have hm := mul_le_mul (geometric_norm_bound n ρ hρ z hz)
    (block_radial_error ρ hρ hρ1 z hz) (norm_nonneg _)
    (Finset.sum_nonneg (fun i _ => pow_nonneg (pow_nonneg hρ _) _))
  have hi := weight_identity (ρ^5) n
  have hn : 0 ≤ (ρ^5)^n := by positivity
  exact hm.trans (by nlinarith)

theorem finite_sum_upper (n : ℕ) (ρ u : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖FiniteFourierKernel.finiteSum n ((ρ:ℂ)*AngularKernel.circle u)‖ ≤
      RadialKernelProfile.profile u+4 := by
  have he : FiniteFourierKernel.finiteSum n ((ρ:ℂ)*AngularKernel.circle u) =
      (∑ i ∈ Finset.range n, (((ρ:ℂ)*AngularKernel.circle u)^5)^i)*block (AngularKernel.circle u)+
      (∑ i ∈ Finset.range n, (((ρ:ℂ)*AngularKernel.circle u)^5)^i)*
        (block ((ρ:ℂ)*AngularKernel.circle u)-block (AngularKernel.circle u)) := by
    rw [FiniteFourierKernel.finiteSum_blocks]
    unfold block
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (weighted_unit_blocks n ρ u hρ hρ1 hu h5u)
    (radial_block_sum_error n ρ hρ hρ1 (AngularKernel.circle u) (AngularKernel.circle_norm u)))

end
end Borwein.AbelRadialBound
