import Borwein.PeriodicSineLower
import Borwein.CuspRectangleBridge

set_option autoImplicit false

namespace Borwein.CuspCellCertificate
noncomputable section

structure Cell where
  m1 : ℕ
  m2 : ℕ
  m3 : ℕ
  s1 : ℚ
  s2 : ℚ
  s3 : ℚ
  deriving Inhabited

def left (i : ℕ) : ℚ := 2+(i:ℚ)/40
def center (i : ℕ) : ℚ := 2+(2*(i:ℚ)+1)/80
def rationalEnvelope (l1 l2 l3 : ℚ) : ℚ :=
  max (-l1) (-(3/5)*l1)+max (-l2) (-(3/5:ℚ)^2*l2)/4+
    max (-l3) (-(3/5:ℚ)^3*l3)/9+13/45

def Valid (i : ℕ) (r : Cell) : Prop :=
  PeriodicSineLower.Checked (center i) r.s1 r.m1 ∧
  PeriodicSineLower.Checked (2*center i) r.s2 r.m2 ∧
  PeriodicSineLower.Checked (3*center i) r.s3 r.m3 ∧
  rationalEnvelope (r.s1-1/80) (r.s2-2/80) (r.s3-3/80) ≤ (9/32)*left i

instance (i : ℕ) (r : Cell) : Decidable (Valid i r) := inferInstanceAs (Decidable
  (PeriodicSineLower.Checked (center i) r.s1 r.m1 ∧
  PeriodicSineLower.Checked (2*center i) r.s2 r.m2 ∧
  PeriodicSineLower.Checked (3*center i) r.s3 r.m3 ∧
  rationalEnvelope (r.s1-1/80) (r.s2-2/80) (r.s3-3/80) ≤ (9/32)*left i))

def lo (i : Fin 160) : ℝ := 2+(i.val:ℝ)/40
def hi (i : Fin 160) : ℝ := 2+(i.val:ℝ)/40+1/40

theorem center_distance (i : Fin 160) (t : ℝ) (hl : lo i ≤ t) (hu : t ≤ hi i) :
    |t-(center i.val:ℝ)| ≤ 1/80 := by
  dsimp [lo,hi] at hl hu
  simp only [center,Rat.cast_add,Rat.cast_ofNat,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem frequency_lower (i : Fin 160) (t : ℝ) (k m : ℕ) (s : ℚ)
    (hl : lo i ≤ t) (hu : t ≤ hi i)
    (h : PeriodicSineLower.Checked ((k:ℚ)*center i.val) s m) :
    (s:ℝ)-(k:ℝ)/80 ≤ Real.sin ((k:ℝ)*t) := by
  have hs := PeriodicSineLower.checked_sound _ _ _ h
  push_cast at hs
  have hc := center_distance i t hl hu
  have hd : |(k:ℝ)*t-(k:ℝ)*(center i.val:ℝ)| ≤ (k:ℝ)/80 := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg k)]
    have hmul := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg k)
    exact hmul.trans_eq (by ring)
  have ht := (Real.abs_sin_sub_sin_le ((k:ℝ)*t) ((k:ℝ)*(center i.val:ℝ))).trans hd
  have hm := (abs_le.mp ht).1
  linarith

theorem valid_sound (i : Fin 160) (r : Cell) (h : Valid i.val r) (t : ℝ)
    (hl : lo i ≤ t) (hu : t ≤ hi i) :
    (r.s1:ℝ)-1/80 ≤ Real.sin t ∧
    (r.s2:ℝ)-2/80 ≤ Real.sin (2*t) ∧
    (r.s3:ℝ)-3/80 ≤ Real.sin (3*t) ∧
    CuspRectangleBridge.envelope ((r.s1:ℝ)-1/80) ((r.s2:ℝ)-2/80) ((r.s3:ℝ)-3/80) ≤ (9/32)*t := by
  obtain ⟨h1,h2,h3,hE⟩ := h
  have hs1 := frequency_lower i t 1 r.m1 r.s1 hl hu (by simpa using h1)
  have hs2 := frequency_lower i t 2 r.m2 r.s2 hl hu h2
  have hs3 := frequency_lower i t 3 r.m3 r.s3 hl hu h3
  norm_num only [Nat.cast_one,Nat.cast_ofNat,one_mul] at hs1 hs2 hs3
  refine ⟨by norm_num at hs1 ⊢; exact hs1,by norm_num at hs2 ⊢; exact hs2,
    by norm_num at hs3 ⊢; exact hs3,?_⟩
  have he : CuspRectangleBridge.envelope ((r.s1:ℝ)-1/80) ((r.s2:ℝ)-2/80) ((r.s3:ℝ)-3/80) ≤
      (9/32:ℝ)*lo i := by
    have hh : (rationalEnvelope (r.s1-1/80) (r.s2-2/80) (r.s3-3/80):ℝ) ≤
        (((9/32)*left i.val:ℚ):ℝ) := by exact_mod_cast hE
    simpa [rationalEnvelope,CuspRectangleBridge.envelope,left,lo] using hh
  exact he.trans (mul_le_mul_of_nonneg_left hl (by norm_num))

theorem cell_cover (t : ℝ) (ht0 : 2 ≤ t) (ht1 : t ≤ 6) :
    ∃ i : Fin 160, lo i ≤ t ∧ t ≤ hi i := by
  by_cases he : t = 6
  · refine ⟨159,?_⟩
    norm_num [lo,hi,he]
  · have hx0 : 0 ≤ 40*t-80 := by linarith
    have hx1 : 40*t-80 < 160 := by
      have htlt : t < 6 := lt_of_le_of_ne ht1 he
      linarith
    have hk : ⌊40*t-80⌋₊ < 160 := (Nat.floor_lt hx0).mpr (by exact_mod_cast hx1)
    refine ⟨⟨⌊40*t-80⌋₊,hk⟩,?_⟩
    have hL := Nat.floor_le hx0
    have hU := Nat.lt_floor_add_one (40*t-80)
    dsimp [lo,hi]
    constructor <;> linarith

end
end Borwein.CuspCellCertificate
