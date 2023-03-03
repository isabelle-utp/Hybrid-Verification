session "Framed_ODEs" = Ordinary_Differential_Equations +
  options [document = false]
  sessions
    "Shallow-Expressions"
    "Hybrid-Library"
    Optics
    CAS_Integration
  theories
    Framed_ODEs

session "Matrix_ODE_Verify" in Matrices = "Framed_ODEs" +
  options [document = false]
  theories
    MTX_Preliminaries
    MTX_Norms
    SQ_MTX
    MTX_Flows

session "Hybrid-Verification" in "Hybrid_Programs" = "Matrix_ODE_Verify" +
  options [document = false]
  theories
    HS_Lens_Spartan
    Real_Arith_Tactics
    HS_CAS_Integration

(*
session "Hybrid-Verification" = Ordinary_Differential_Equations +
  options [quick_and_dirty, document = pdf, document_output = "output"]
  sessions
    "Shallow-Expressions"
    "Hybrid-Library"
    Optics
    CAS_Integration
  directories
    Matrices
  (*theories [document = false]
    HS_Preliminaries
    HS_ODEs
    HS_VC_Spartan
    HS_Lens_ODEs
    HS_Lens_Spartan
    HS_Lie_Derivatives
    Real_Arith_Tactics
    "Matrices/MTX_Preliminaries"
    "Matrices/MTX_Norms"
    "Matrices/SQ_MTX"
    "Matrices/MTX_Flows"*)
  theories
    ARCH2022_Examples
    "Matrices/MTX_Examples"
  document_files
    "root.tex"
*)
