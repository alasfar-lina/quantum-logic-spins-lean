def zUp : V := !₂[1, 0]
def zDn : V := !₂[0, 1]
def xUp : V := !₂[1, 1]
def xDn : V := !₂[1, -1]

def Zup : Submodule ℂ V := ℂ ∙ zUp
def Zdn : Submodule ℂ V := ℂ ∙ zDn
def Xup : Submodule ℂ V := ℂ ∙ xUp
def Xdn : Submodule ℂ V := ℂ ∙ xDn
