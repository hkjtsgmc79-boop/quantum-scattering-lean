import QuantumScattering.RectangularBridge
noncomputable section
open QuantumScattering
example (p : QuantumTunneling.RectangularParameters) (a b : ℂ) :
    RectangularBridge.rawWave p a b=p.coherentWave a b :=
  RectangularBridge.wave_eq_legacy p a b
example (p : QuantumTunneling.RectangularParameters) :
    (RectangularBridge.model p).problem.channels.transmission=p.layer.T :=
  RectangularBridge.transmission_eq_legacy p
