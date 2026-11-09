module

public import ArtinMatthews.MarkedTypeIIDyadDeltaTerm


set_option backward.privateInPublic true
@[expose] public section

/-! The exact original occupied determinant sum is the actual coprime
scalar delta sum. This reindex keeps the coprime label restriction. -/
namespace ArtinMatthews
open scoped BigOperators ComplexConjugate Classical
noncomputable section

theorem giantMarkedEndpoints_double_sum {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M N : Finset ℕ) (f : MarkedTypeIIEndpoint → MarkedTypeIIEndpoint → ℂ) :
    (∑ u∈giantMarkedEndpoints P M N,∑ v∈giantMarkedEndpoints P M N,f u v)=
      ∑ a∈markedMajorLabelSet P,∑ b∈markedMajorLabelSet P,
        ∑ v∈M.product N,∑ u∈M.product N,
          f (giantMarkedEndpoint a v.1 v.2) (giantMarkedEndpoint b u.1 u.2) := by
  simp_rw [giantMarkedEndpoints_sum]
  have hp (F : ℕ×ℕ → ℂ) : (∑ v∈M.product N,F v)=∑ m∈M,∑ n∈N,F (m,n) :=
    Finset.sum_product M N F
  simp_rw [hp]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [Finset.sum_comm (s:=N) (t:=markedMajorLabelSet P)]
  rw [Finset.sum_comm (s:=M) (t:=markedMajorLabelSet P)]

theorem markedTypeII_occupied_determinant_eq_coprime_delta {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (Y : ℝ) (ψ : ℝ → ℂ) (M N : Finset ℕ) (α β : ℕ → ℂ)
    (hψ : ∀ t∈Set.Icc (-4:ℝ) 4,ψ t=1) :
    markedTypeIIDeterminantSum (markedTypeIIOccupiedLabelEndpoints P Y M N)
      (markedTypeIILabelEndpointCoefficient P Y α β) =
    markedPhysicalCoprimeScalarDetectorSum P M N markedTypeIILabelCutoff Y
      (markedRawEdgeDeltaDetector ψ Y) α β := by
  let L := markedMajorLabelSet P
  let mass := (markedMajorLabelMass P:ℂ)^2
  let G (b a : ℕ) := markedPhysicalScalarDetectorBlock M N markedTypeIILabelCutoff Y
    (markedRawEdgeDeltaDetector ψ Y) α β b a
  have hRight : markedPhysicalCoprimeScalarDetectorSum P M N markedTypeIILabelCutoff Y
      (markedRawEdgeDeltaDetector ψ Y) α β =
      ∑ a∈L,∑ b∈L,mass*(if b.Coprime a then G b a else 0) := by
    calc
      _ = mass*(∑ b∈L,∑ a∈L,if b.Coprime a then G b a else 0) := by
        unfold markedPhysicalCoprimeScalarDetectorSum markedPhysicalCoprimeLabelPairs
        rw [Finset.sum_filter]
        exact congrArg (fun z : ℂ => mass*z)
          (Finset.sum_product L L (fun p => if p.1.Coprime p.2 then G p.1 p.2 else 0))
      _ = mass*(∑ a∈L,∑ b∈L,if b.Coprime a then G b a else 0) := by rw [Finset.sum_comm]
      _ = _ := by simp only [Finset.mul_sum]
  rw [markedTypeII_occupied_determinant_eq_full,hRight]
  unfold markedTypeIIDeterminantSum
  rw [giantMarkedEndpoints_double_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hcop : a.Coprime b
  · rw [ite_eq_left hcop.symm]
    unfold G markedPhysicalScalarDetectorBlock
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro u _
    have hc : (giantMarkedEndpoint a v.1 v.2).label.Coprime
        (giantMarkedEndpoint b u.1 u.2).label := hcop
    exact (ite_cond_congr (propext (and_iff_right hc))).trans
      (markedTypeII_dyad_delta_term P Y ψ α β hψ a b v.1 v.2 u.1 u.2)
  · have hn : ¬b.Coprime a := fun h => hcop h.symm
    rw [ite_eq_right hn,mul_zero]
    apply Finset.sum_eq_zero
    intro v _
    apply Finset.sum_eq_zero
    intro u _
    exact ite_eq_right (fun h => hcop h.1)

end
end ArtinMatthews
