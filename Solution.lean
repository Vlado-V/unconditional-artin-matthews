module

public import ArtinMatthews.FullMainActual

@[expose] public section

namespace ArtinMatthewsPaper

open ArtinMatthews

/-- Theorem 1.1 of the accompanying Artin–Matthews paper. -/
theorem main_result :
  ∀ S : Finset ℤ, AdmissibleBases S →
    ((¬ ObstructionA S ∧ ¬ ObstructionB S) →
      PositiveDyadicLowerBound S ∧ PositiveRealLowerRelativePrimeDensity S) ∧
    ((ObstructionA S ∨ ObstructionB S) → (SimultaneousPrimitivePrimes S).Finite) := ArtinMatthews.main_result

end ArtinMatthewsPaper
