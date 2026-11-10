module

public import ArtinMatthews.AdelicCharacterData
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.QuadraticWeil

open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

theorem completion_nondiscrete (F : Type) [Field F] [NumberField F] (v : ArchimedeanAdeles.Construction.Places F) :
    ¬ DiscreteTopology (ArchimedeanAdeles.Construction.Completion F v) := by
  intro h
  let : DiscreteTopology (ArchimedeanAdeles.Construction.Completion F v) := h
  cases v with
  | inl v =>
      rcases v.isReal_or_isComplex with hv | hv
      · let : DiscreteTopology ℝ :=
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.discreteTopology
        have : Subsingleton ℝ := subsingleton_of_preconnected_totallyDisconnected
        exact zero_ne_one (Subsingleton.elim (0 : ℝ) 1)
      · let : DiscreteTopology ℂ :=
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.discreteTopology
        have : Subsingleton ℂ := subsingleton_of_preconnected_totallyDisconnected
        exact zero_ne_one (Subsingleton.elim (0 : ℂ) 1)
  | inr v =>
      let : CharZero (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
      have he : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
          Metric.closedBall (0 : v.adicCompletion F) 1 := by
        ext x
        simp only [Metric.mem_closedBall, dist_zero_right,
          Valued.toNormedField.norm_le_one_iff]
        rfl
      have hc : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [he]
        exact isCompact_closedBall _ _
      have hf := hc.finite_of_discrete
      have hinf : Set.Infinite (Set.range (fun z : ℤ => (z : v.adicCompletion F))) :=
        Set.infinite_range_of_injective Int.cast_injective
      apply hinf
      apply hf.subset
      rintro _ ⟨z, rfl⟩
      exact intCast_mem (v.adicCompletionIntegers F).toSubring z

end

end ArtinMatthews.QuadraticWeil
