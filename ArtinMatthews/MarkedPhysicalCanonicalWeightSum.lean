module

public import ArtinMatthews.MarkedPhysicalIncidenceRootSum
public import ArtinMatthews.MarkedPhysicalRootTargetReindex


set_option backward.privateInPublic true
@[expose] public section

/-! Finite canonical-root summation and nonnegative target extension.
No physical or analytic estimate is an input. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalCanonicalWeight_sum
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) (S : ℕ) [NeZero S] (A B C D : ℝ)
    (d b a : ℤ) (R Q : ℝ) (ψ : ℝ → ℂ)
    (E : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → (ℤ × ℤ) → Prop) :
    (∑ r : MarkedPhysicalCanonicalRoot S A B C D,
      ∑ z ∈ markedPhysicalRootTargetWindow d R Y,
        if E r.1 z then ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ *
          (if |markedMinorIntegerTau
            (((markedPhysicalCanonicalCompletion r).1 : ℝ)/((markedPhysicalCanonicalRootPosition r).1 : ℝ)) z| ≤ 16 then
            markedRawBadRootArcMajorant e x d₀ Y source
              ((((markedPhysicalCanonicalCompletion r).1 : ℝ)/((markedPhysicalCanonicalRootPosition r).1 : ℝ)) :
                AddCircle (1 : ℝ)) else 0)
        else 0) =
      markedPhysicalRootIncidenceMajorantSum e x source d₀ Y S A B C D d b a R Q ψ E := by
  rw [Fintype.sum_sigma]
  unfold markedPhysicalRootIncidenceMajorantSum
  apply Finset.sum_congr rfl
  intro g _
  have h := Finset.sum_coe_sort
    (fixedURootMatrixBoxPoints g A B 0 1 C D true true true true true true)
    (fun p : Σ _u : ℤ,ℤ × ℤ => ∑ z ∈ markedPhysicalRootTargetWindow d R Y,
      if E g z then ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ *
        (if |markedMinorIntegerTau ((p.2.1 : ℝ)/(p.1 : ℝ)) z| ≤ 16 then
          markedRawBadRootArcMajorant e x d₀ Y source
            (((p.2.1 : ℝ)/(p.1 : ℝ)) : AddCircle (1 : ℝ)) else 0)
      else 0)
  calc
    _ = ∑ p : ↥(fixedURootMatrixBoxPoints g A B 0 1 C D true true true true true true),
      ∑ z ∈ markedPhysicalRootTargetWindow d R Y,
        if E g z then ‖markedBanEdgeKernel ψ Q Y b a (z.2/d)‖ *
          (if |markedMinorIntegerTau (((p.1).2.1 : ℝ)/((p.1).1 : ℝ)) z| ≤ 16 then
            markedRawBadRootArcMajorant e x d₀ Y source
              ((((p.1).2.1 : ℝ)/((p.1).1 : ℝ)) : AddCircle (1 : ℝ)) else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro z _
      dsimp only [markedPhysicalCanonicalCompletion,markedPhysicalCanonicalRootPosition,fixedURootFirstColumn]
      rfl
    _ = _ := h

theorem markedPhysical_sum_indicator_le {ι : Type*} (s t : Finset ι) (f : ι → ℝ)
    (hf : ∀ z ∈ t,0 ≤ f z) :
    (∑ z ∈ s,if z ∈ t then f z else 0) ≤ ∑ z ∈ t,f z := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz _
    exact hf z hz

end ArtinMatthews
