module

public import ArtinMatthews.FixedURootBoxMain
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# The reciprocal determinant-one coordinates

The involution `(u,c;v,d) ↦ (v,v-d;u,u-c)` switches the two positive
coordinate scales. Its canonical root coordinate is `1-c/u-1/(uv)`.
All statements here concern the actual integer determinant and finite boxes.
-/

namespace ArtinMatthews

open OAI.Erdos970 ErdosHyperbolaError

theorem fixedURootReciprocal_det {u c v d : ℤ} (hdet : u*d-v*c = 1) :
    v*(u-c)-u*(v-d) = 1 := by
  linear_combination hdet

/-- The canonical completion stays strictly between zero and the other scale. -/
theorem fixedURootReciprocal_completion_bounds {u c v d : ℤ}
    (hu : 1 < u) (hv : 1 < v) (hc₀ : 0 ≤ c) (hc₁ : c ≤ u)
    (hdet : u*d-v*c = 1) : 0 < c ∧ c < u ∧ 0 < d ∧ d < v := by
  have hcpos : 0 < c := by
    by_contra h
    have hc : c = 0 := by omega
    rw [hc,mul_zero,sub_zero] at hdet
    have hdiv : u ∣ 1 := ⟨d,hdet.symm⟩
    have huabs : u.natAbs = 1 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hdiv
    have : u ≤ 1 := by simpa [Int.natCast_natAbs,abs_of_nonneg (by omega : 0 ≤ u)] using
      (show (u.natAbs : ℤ) ≤ 1 by exact_mod_cast huabs.le)
    omega
  have hclt : c < u := by
    by_contra h
    have hc : c = u := by omega
    rw [hc] at hdet
    have hdiv : u ∣ 1 := ⟨d-v,by linear_combination -hdet⟩
    have hule : u.natAbs ≤ 1 := Nat.le_of_dvd (by norm_num) (Int.natAbs_dvd_natAbs.mpr hdiv)
    have : u ≤ 1 := by simpa [Int.natCast_natAbs,abs_of_nonneg (by omega : 0 ≤ u)] using
      (show (u.natAbs : ℤ) ≤ 1 by exact_mod_cast hule)
    omega
  have hdpos : 0 < d := by nlinarith
  have hcv : c ≤ u-1 := by omega
  have hdlt : d < v := by nlinarith
  exact ⟨hcpos,hclt,hdpos,hdlt⟩

/-- Determinant one makes the integral completion unique and gives its literal quotient. -/
theorem fixedURootReciprocal_completion_eq {u c v d : ℤ}
    (hu : u ≠ 0) (hdet : u*d-v*c = 1) : (1+v*c)/u = d :=
  Int.ediv_eq_of_eq_mul_right hu (by linear_combination -hdet)

/-- The exact displacement of the reciprocal root coordinate. -/
theorem fixedURootReciprocal_ratio {u c v d : ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hdet : u*d-v*c = 1) :
    ((v-d : ℤ) : ℝ)/(v : ℝ) = 1-(c : ℝ)/(u : ℝ)-1/((u : ℝ)*(v : ℝ)) := by
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hd : (u : ℝ)*(d : ℝ)-(v : ℝ)*(c : ℝ) = 1 := by exact_mod_cast hdet
  push_cast
  field_simp
  nlinarith

/-- The integer triple map uses the determinant-forced completion, rather than
an independently chosen representative. -/
def fixedURootReciprocalPoint (x : Σ _u : ℤ, ℤ × ℤ) : Σ _u : ℤ, ℤ × ℤ :=
  ⟨x.2.2,(x.2.2-(1+x.2.2*x.2.1)/x.1,x.1)⟩

theorem fixedURootReciprocalPoint_completion {u c v d : ℤ}
    (hu : u ≠ 0) (hdet : u*d-v*c = 1) :
    fixedURootReciprocalPoint ⟨u,(c,v)⟩ = ⟨v,(v-d,u)⟩ := by
  simp only [fixedURootReciprocalPoint,fixedURootReciprocal_completion_eq hu hdet]

theorem fixedURootReciprocalPoint_involutive {u c v d : ℤ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hdet : u*d-v*c = 1) :
    fixedURootReciprocalPoint (fixedURootReciprocalPoint ⟨u,(c,v)⟩) = ⟨u,(c,v)⟩ := by
  rw [fixedURootReciprocalPoint_completion hu hdet,
    fixedURootReciprocalPoint_completion hv (fixedURootReciprocal_det hdet)]
  simp

theorem fixedURootReciprocal_residues {S : ℕ} {u c v d u₀ c₀ v₀ d₀ : ℤ}
    (hu : Int.ModEq (S : ℤ) u u₀) (hc : Int.ModEq (S : ℤ) c c₀)
    (hv : Int.ModEq (S : ℤ) v v₀) (hd : Int.ModEq (S : ℤ) d d₀) :
    Int.ModEq (S : ℤ) v v₀ ∧ Int.ModEq (S : ℤ) (v-d) (v₀-d₀) ∧
      Int.ModEq (S : ℤ) u u₀ ∧ Int.ModEq (S : ℤ) (u-c) (u₀-c₀) :=
  ⟨hv,hv.sub hd,hu,hu.sub hc⟩

theorem fixedURootReciprocal_residue_det {S : ℕ} {u₀ c₀ v₀ d₀ : ℤ}
    (hdet : Int.ModEq (S : ℤ) (u₀*d₀-c₀*v₀) 1) :
    Int.ModEq (S : ℤ) (v₀*(u₀-c₀)-(v₀-d₀)*u₀) 1 := by
  convert hdet using 1; ring

/-- Endpoint flags in the finite real interval have their literal meaning. -/
theorem fixedURootReciprocal_mem_interval {x y : ℝ} {lc rc : Bool} {z : ℤ} :
    z ∈ realIntervalIntegers x y lc rc ↔
      (if lc then x ≤ (z : ℝ) else x < (z : ℝ)) ∧
      (if rc then (z : ℝ) ≤ y else (z : ℝ) < y) := by
  rw [realIntervalIntegers,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have hl : x ≤ (z : ℝ) := by
      cases lc
      · exact le_of_lt h.1
      · exact h.1
    have hr : (z : ℝ) ≤ y := by
      cases rc
      · exact le_of_lt h.2
      · exact h.2
    exact ⟨⟨Int.ceil_le.mpr hl,Int.le_floor.mpr hr⟩,h⟩

theorem fixedURootReciprocal_interval_bounds {x y : ℝ} {lc rc : Bool} {z : ℤ}
    (hz : z ∈ realIntervalIntegers x y lc rc) : x ≤ (z : ℝ) ∧ (z : ℝ) ≤ y := by
  obtain ⟨hl,hr⟩ := fixedURootReciprocal_mem_interval.mp hz
  constructor
  · cases lc
    · exact le_of_lt hl
    · exact hl
  · cases rc
    · exact le_of_lt hr
    · exact hr

theorem fixedURootReciprocal_scaled_interval {w α β : ℝ} (hw : 0 < w)
    (lc rc : Bool) (c : ℤ) :
    c ∈ realIntervalIntegers (w*α) (w*β) lc rc ↔
      (if lc then α ≤ (c : ℝ)/w else α < (c : ℝ)/w) ∧
      (if rc then (c : ℝ)/w ≤ β else (c : ℝ)/w < β) := by
  rw [fixedURootReciprocal_mem_interval]
  simp only [le_div_iff₀ hw,lt_div_iff₀ hw,div_le_iff₀ hw,div_lt_iff₀ hw,mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Membership of the actual finite box is exactly an integral determinant-one
completion with all four prescribed matrix residues. -/
theorem fixedURootReciprocal_mem_box {S : ℕ} {u₀ c₀ v₀ d₀ u c v : ℤ}
    (hu : 0 < u) (A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool) :
    (⟨u,(c,v)⟩ : Σ _u : ℤ, ℤ × ℤ) ∈
      fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV ↔
      u ∈ realIntervalIntegers A B lcU rcU ∧
      c ∈ realIntervalIntegers ((u : ℝ)*α) ((u : ℝ)*β) lcC rcC ∧
      v ∈ realIntervalIntegers C D lcV rcV ∧
      Int.ModEq (S : ℤ) u u₀ ∧ Int.ModEq (S : ℤ) c c₀ ∧
      Int.ModEq (S : ℤ) v v₀ ∧
      ∃ d : ℤ, u*d-v*c = 1 ∧ Int.ModEq (S : ℤ) d d₀ := by
  have huabs : (u.natAbs : ℤ) = u := by rw [Int.natCast_natAbs,abs_of_pos hu]
  have huabsR : (u.natAbs : ℝ) = (u : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) huabs
  simp only [fixedURootBoxPoints,Finset.mem_sigma,fixedURootBoxIndices,
    fixedURootPairs,Finset.mem_filter,huabsR]
  rw [fixedURoot_completion_iff]
  simp only [huabs]
  rw [show (c,v) ∈ (realIntervalIntegers ((u : ℝ)*α) ((u : ℝ)*β) lcC rcC).product
      (realIntervalIntegers C D lcV rcV) ↔
      c ∈ realIntervalIntegers ((u : ℝ)*α) ((u : ℝ)*β) lcC rcC ∧
      v ∈ realIntervalIntegers C D lcV rcV from Finset.mem_product]
  tauto

/-- The reciprocal displacement is uniformly bounded by the lower-coordinate
rectangle scales. -/
theorem fixedURootReciprocal_shift_le {A C : ℝ} {u v : ℤ}
    (hA : 0 < A) (hC : 0 < C) (hu : A ≤ (u : ℝ)) (hv : C ≤ (v : ℝ)) :
    1/((u : ℝ)*(v : ℝ)) ≤ 1/(A*C) := by
  exact one_div_le_one_div_of_le (mul_pos hA hC)
    (mul_le_mul hu hv hC.le (hA.le.trans hu))

end ArtinMatthews
