import Mathlib.Data.Finset.Card
import Aesop
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace Borwein.ExplicitLargeNZeroSet

def lowerZeros (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun j => 5*j+3) ∪
  (Finset.range n).image (fun j => 5*j+4) ∪
  {7,5*n+8,5*n+9}

def zeros (n : ℕ) : Finset ℕ :=
  lowerZeros n ∪ (lowerZeros n).image (fun m => 10*n^2-m)

private theorem mem_three (n m : ℕ) :
    m ∈ (Finset.range n).image (fun j => 5*j+3) ↔ m%5=3 ∧ m<5*n := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    simp only [Finset.mem_range] at hj
    constructor <;> omega
  · rintro ⟨hr,hm⟩
    refine ⟨m/5,Finset.mem_range.mpr ?_,?_⟩
    · omega
    · omega

private theorem mem_four (n m : ℕ) :
    m ∈ (Finset.range n).image (fun j => 5*j+4) ↔ m%5=4 ∧ m<5*n := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    simp only [Finset.mem_range] at hj
    constructor <;> omega
  · rintro ⟨hr,hm⟩
    refine ⟨m/5,Finset.mem_range.mpr ?_,?_⟩
    · omega
    · omega

theorem mem_lowerZeros (n m : ℕ) :
    m ∈ lowerZeros n ↔
      (((m%5=3 ∨ m%5=4) ∧ m<5*n) ∨
        m=7 ∨ m=5*n+8 ∨ m=5*n+9) := by
  rw [lowerZeros,Finset.mem_union,Finset.mem_union,mem_three,mem_four]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  aesop

private theorem three_injective : Function.Injective (fun j : ℕ => 5*j+3) := by
  intro a b h
  change 5*a+3 = 5*b+3 at h
  omega

private theorem four_injective : Function.Injective (fun j : ℕ => 5*j+4) := by
  intro a b h
  change 5*a+4 = 5*b+4 at h
  omega

private theorem progressions_disjoint (n : ℕ) :
    Disjoint ((Finset.range n).image (fun j => 5*j+3))
      ((Finset.range n).image (fun j => 5*j+4)) := by
  rw [Finset.disjoint_left]
  intro m h3 h4
  have h3' := (mem_three n m).mp h3
  have h4' := (mem_four n m).mp h4
  omega

private theorem progressions_special_disjoint (n : ℕ) :
    Disjoint
      ((Finset.range n).image (fun j => 5*j+3) ∪
        (Finset.range n).image (fun j => 5*j+4))
      ({7,5*n+8,5*n+9} : Finset ℕ) := by
  rw [Finset.disjoint_left]
  intro m hm hs
  rw [Finset.mem_union] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hm with hm | hm
  · have hh := (mem_three n m).mp hm
    omega
  · have hh := (mem_four n m).mp hm
    omega

private theorem special_card (n : ℕ) :
    ({7,5*n+8,5*n+9} : Finset ℕ).card=3 := by
  have h7 : 7 ∉ ({5*n+8,5*n+9} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have h8 : 5*n+8 ∉ ({5*n+9} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  rw [Finset.card_insert_of_notMem h7,Finset.card_insert_of_notMem h8,
    Finset.card_singleton]

theorem lowerZeros_card (n : ℕ) : (lowerZeros n).card=2*n+3 := by
  rw [lowerZeros,Finset.card_union_of_disjoint (progressions_special_disjoint n),
    Finset.card_union_of_disjoint (progressions_disjoint n),
    Finset.card_image_iff.mpr (fun _ _ _ _ h => three_injective h),
    Finset.card_image_iff.mpr (fun _ _ _ _ h => four_injective h),
    Finset.card_range,special_card]
  omega

theorem lowerZeros_lt_half (n : ℕ) (hn : 2 ≤ n) {m : ℕ}
    (hm : m ∈ lowerZeros n) : m < 5*n^2 := by
  rw [mem_lowerZeros] at hm
  rcases hm with ⟨_,hm⟩ | rfl | rfl | rfl
  · exact hm.trans_le (by nlinarith)
  all_goals nlinarith

private theorem reflection_card (n : ℕ) (hn : 2 ≤ n) :
    ((lowerZeros n).image (fun m => 10*n^2-m)).card=(lowerZeros n).card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  change 10*n^2-a = 10*n^2-b at hab
  have ha' := lowerZeros_lt_half n hn ha
  have hb' := lowerZeros_lt_half n hn hb
  omega

private theorem reflection_disjoint (n : ℕ) (hn : 2 ≤ n) :
    Disjoint (lowerZeros n) ((lowerZeros n).image (fun m => 10*n^2-m)) := by
  rw [Finset.disjoint_left]
  intro m hm hreflection
  obtain ⟨k,hk,hkm⟩ := Finset.mem_image.mp hreflection
  have hm' := lowerZeros_lt_half n hn hm
  have hk' := lowerZeros_lt_half n hn hk
  omega

theorem zeros_card (n : ℕ) (hn : 2 ≤ n) : (zeros n).card=4*n+6 := by
  rw [zeros,Finset.card_union_of_disjoint (reflection_disjoint n hn),
    reflection_card n hn,lowerZeros_card]
  omega

end Borwein.ExplicitLargeNZeroSet
