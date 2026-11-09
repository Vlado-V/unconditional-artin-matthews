module

public import ArtinMatthews.MarkedMemoryActualChoiceMass
public import ArtinMatthews.MarkedMemoryPathCapacityTail
public import ArtinMatthews.MarkedMemoryOrphanTailDecay


set_option backward.privateInPublic true
@[expose] public section

/-! The actual small-B capacity correction has every logarithmic saving,
uniformly over the actual compatible finite path choices. B remains
ceil(log(x)^2), and the signed scalar error is the original omitted sum. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)

def markedMemoryPathCapacityAbsoluteError (q : ℝ) (B : ℕ) : ℝ :=
  ∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
      MarkedMemoryPathChoicesCompatible d hZ c},
    if MarkedMemoryPathCapacity hZ d c.1 c.2 B then 0 else
      |markedMemoryPathPrimeChoiceWeight hZ d q c.1|

def markedMemoryPathCapacitySignedError (q : ℝ) (B : ℕ) : ℝ :=
  ∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
      MarkedMemoryPathChoicesCompatible d hZ c},
    if MarkedMemoryPathCapacity hZ d c.1 c.2 B then 0 else
      markedMemoryPathPrimeChoiceWeight hZ d q c.1

theorem markedMemoryActualCapacityTail_envelope
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ),0≤q → q≤1 →
      ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
        (d : MarkedMemoryActivePathData (markedRawActualPrimeBand e x)
          ⌊(Real.log x)^(1/100:ℝ)⌋₊ Z (markedMemoryMomentLength x)),
      markedMemoryPathCapacityAbsoluteError hZ d q (markedDirtyMemoryCutoff x)≤
        markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x ∧
      |markedMemoryPathCapacitySignedError hZ d q (markedDirtyMemoryCutoff x)|≤
        markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x := by
  filter_upwards [markedMemoryActualPathChoiceMass_bounds e he,
    markedMemoryOrphan_active_budget (Fintype.card J),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hm hb hlog
  intro q hq0 hq1 Z hZ d
  have hmasses := hm q hq0 hq1 Z hZ d
  have hsq := markedMemoryMomentLength_sq_bound hlog
  have hExp : 2*markedMemoryPathInactiveAtomMass d q*((markedMemoryMomentLength x:ℝ)+1)^2≤
      64*(Fintype.card J:ℝ)*Real.log x := by
    have h1 := mul_le_mul_of_nonneg_right hmasses.2.1 (sq_nonneg ((markedMemoryMomentLength x:ℝ)+1))
    have h2 := mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (by norm_num : (0:ℝ)≤4) (Nat.cast_nonneg (Fintype.card J)))
    nlinarith
  have hbound : markedMemoryPathActiveChoiceAbsoluteMass hZ d q *
      Real.exp (2*markedMemoryPathInactiveAtomMass d q*((markedMemoryMomentLength x:ℝ)+1)^2)/
        (2:ℝ)^(markedDirtyMemoryCutoff x/2+1)≤
      markedMemoryOrphanTailEnvelope (80*(Fintype.card J:ℝ)) 1 x := by
    calc
      _ ≤ Real.exp (16*(Fintype.card J:ℝ)*Real.log x)*
          Real.exp (64*(Fintype.card J:ℝ)*Real.log x)/(2:ℝ)^(markedDirtyMemoryCutoff x/2+1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul hmasses.1 (Real.exp_le_exp.mpr hExp) (Real.exp_nonneg _) (Real.exp_nonneg _))
          (by positivity)
      _ = _ := by
        rw [← Real.exp_add]
        unfold markedMemoryOrphanTailEnvelope
        rw [Real.rpow_one]
        congr 2
        ring
  exact ⟨(markedMemoryPathCapacity_absolute_error hZ d q hq0 hq1 hmasses.2.2
      2 (by norm_num) (markedDirtyMemoryCutoff x/2) hb).trans hbound,
    (markedMemoryPathCapacity_signed_error hZ d q hq0 hq1 hmasses.2.2
      2 (by norm_num) (markedDirtyMemoryCutoff x/2) hb).trans hbound⟩

theorem markedMemoryActualCapacityTail_log_saving
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (G : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ),0≤q → q≤1 →
      ∀ (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
        (d : MarkedMemoryActivePathData (markedRawActualPrimeBand e x)
          ⌊(Real.log x)^(1/100:ℝ)⌋₊ Z (markedMemoryMomentLength x)),
      markedMemoryPathCapacityAbsoluteError hZ d q (markedDirtyMemoryCutoff x)≤(Real.log x)^(-G) ∧
      |markedMemoryPathCapacitySignedError hZ d q (markedDirtyMemoryCutoff x)|≤(Real.log x)^(-G) := by
  filter_upwards [markedMemoryActualCapacityTail_envelope e he,
    markedMemoryOrphanTailEnvelope_log_saving (80*(Fintype.card J:ℝ)) 1 G (by norm_num)] with x hx hs
  intro q hq0 hq1 Z hZ d
  exact ⟨(hx q hq0 hq1 Z hZ d).1.trans hs,(hx q hq0 hq1 Z hZ d).2.trans hs⟩

end
end ArtinMatthews
