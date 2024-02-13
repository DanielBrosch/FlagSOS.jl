using FlagSOS, Test
HarmG = HarmonicFlag{Graph}

@test HarmG(Bool[0 1; 1 0]) == labelCanonically(HarmG(Bool[0 1 0; 1 0 0; 0 0 0]))

