import Paper2.Certificates.Q6Coverage.OrbitCore

namespace Paper2.Certificates.Q6.Coverage

def officialRow0 : State := ![.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero]

def officialRow1 : State := ![.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.pos 9,.pos 10,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero]

def officialRow2 : State := ![.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.pos 8,.neg 8,.pos 10,.neg 10,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero]

def officialRow3 : State := ![.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.pos 8,.pos 9,.pos 10,.pos 11,.zero,.zero,.zero,.zero,.zero,.zero,.zero,.zero]

def officialRow4 : State := ![.zero,.zero,.zero,.zero,.zero,.zero,.pos 6,.pos 6,.zero,.neg 6,.pos 6,.zero,.neg 6,.neg 6,.zero,.zero,.zero,.zero,.zero,.zero]

def officialRow5 : State := ![.zero,.zero,.zero,.zero,.zero,.zero,.pos 6,.pos 6,.zero,.neg 6,.pos 10,.zero,.neg 10,.neg 10,.zero,.zero,.zero,.zero,.zero,.zero]

def officialRow6 : State := ![.zero,.zero,.zero,.zero,.zero,.zero,.pos 6,.pos 7,.zero,.neg 7,.pos 10,.zero,.neg 10,.pos 13,.zero,.zero,.zero,.zero,.zero,.zero]

def officialRow7 : State := ![.zero,.zero,.zero,.zero,.zero,.zero,.pos 6,.pos 7,.zero,.pos 9,.pos 10,.zero,.pos 12,.pos 13,.zero,.zero,.zero,.zero,.zero,.zero]

def officialRow8 : State := ![.zero,.zero,.zero,.zero,.zero,.pos 5,.neg 5,.neg 5,.pos 8,.zero,.zero,.pos 11,.pos 12,.pos 12,.neg 12,.zero,.zero,.zero,.zero,.zero]

def officialRow9 : State := ![.zero,.zero,.zero,.zero,.zero,.pos 5,.neg 5,.pos 7,.pos 8,.zero,.zero,.pos 11,.pos 12,.pos 13,.neg 13,.zero,.zero,.zero,.zero,.zero]

def officialRow10 : State := ![.zero,.zero,.zero,.zero,.zero,.pos 5,.pos 6,.pos 7,.pos 8,.zero,.zero,.pos 11,.pos 12,.pos 13,.pos 14,.zero,.zero,.zero,.zero,.zero]

def officialRow11 : State := ![.pos 0,.neg 0,.neg 0,.neg 0,.neg 0,.neg 0,.pos 0,.neg 0,.neg 0,.pos 0,.neg 0,.pos 0,.pos 0,.neg 0,.pos 0,.pos 0,.pos 0,.pos 0,.pos 0,.neg 0]

def officialRow12 : State := ![.pos 0,.neg 0,.neg 0,.neg 0,.neg 0,.neg 0,.pos 0,.neg 0,.neg 0,.pos 0,.pos 0,.neg 0,.neg 0,.pos 0,.neg 0,.neg 0,.neg 0,.neg 0,.neg 0,.pos 0]

def officialRow13 : State := ![.pos 0,.neg 0,.neg 0,.neg 0,.neg 0,.neg 0,.pos 0,.pos 0,.neg 0,.pos 0,.neg 0,.pos 0,.neg 0,.neg 0,.pos 0,.pos 0,.pos 0,.pos 0,.pos 0,.neg 0]

def officialRow14 : State := ![.pos 0,.neg 0,.neg 0,.neg 0,.neg 0,.neg 0,.pos 0,.pos 7,.neg 0,.pos 0,.neg 0,.pos 0,.pos 12,.neg 0,.pos 0,.pos 0,.pos 0,.pos 0,.pos 0,.neg 0]

def officialRow15 : State := ![.pos 0,.neg 0,.neg 0,.neg 0,.neg 0,.pos 0,.pos 0,.neg 0,.pos 0,.pos 0,.pos 0,.pos 0,.neg 0,.pos 0,.pos 0,.neg 0,.neg 0,.neg 0,.neg 0,.pos 0]

def officialRow16 : State := ![.pos 0,.neg 0,.neg 0,.neg 0,.neg 0,.pos 0,.pos 0,.pos 7,.neg 7,.pos 0,.pos 0,.pos 11,.neg 11,.pos 0,.pos 0,.neg 0,.neg 0,.neg 0,.neg 0,.pos 0]

def officialRow17 : State := ![.pos 0,.neg 0,.neg 0,.pos 0,.neg 0,.pos 0,.neg 0,.pos 0,.pos 0,.neg 0,.pos 0,.neg 0,.neg 0,.pos 0,.neg 0,.pos 0,.neg 0,.pos 0,.pos 0,.neg 0]

def officialRow18 : State := ![.pos 0,.neg 0,.neg 0,.pos 0,.neg 0,.pos 0,.neg 0,.pos 0,.pos 0,.pos 9,.pos 10,.neg 0,.neg 0,.pos 0,.neg 0,.pos 0,.neg 0,.pos 0,.pos 0,.neg 0]

def officialRow19 : State := ![.pos 0,.neg 0,.neg 0,.pos 0,.neg 0,.pos 0,.neg 0,.pos 7,.neg 7,.neg 0,.pos 0,.pos 11,.neg 11,.pos 0,.neg 0,.pos 0,.neg 0,.pos 0,.pos 0,.neg 0]

def officialRow20 : State := ![.pos 0,.neg 0,.neg 0,.pos 0,.neg 0,.pos 0,.neg 0,.pos 7,.pos 8,.neg 0,.pos 0,.pos 11,.pos 12,.pos 0,.neg 0,.pos 0,.neg 0,.pos 0,.pos 0,.neg 0]

def officialRow21 : State := ![.pos 0,.neg 0,.neg 0,.pos 0,.neg 0,.pos 5,.neg 0,.pos 0,.pos 5,.neg 5,.pos 5,.neg 5,.neg 0,.pos 0,.neg 5,.pos 0,.neg 0,.pos 0,.pos 0,.neg 0]

def officialRow22 : State := ![.pos 0,.neg 0,.neg 0,.pos 0,.pos 4,.neg 4,.neg 0,.pos 0,.neg 4,.pos 9,.neg 4,.pos 9,.neg 0,.pos 0,.pos 9,.neg 9,.neg 0,.pos 0,.pos 0,.neg 0]

def officialRow23 : State := ![.pos 0,.neg 0,.neg 0,.pos 0,.pos 4,.neg 4,.neg 0,.pos 0,.neg 4,.pos 9,.pos 10,.pos 4,.neg 0,.pos 0,.pos 4,.neg 4,.neg 0,.pos 0,.pos 0,.neg 0]

def officialRows : Fin 24 → State := ![officialRow0,officialRow1,officialRow2,officialRow3,officialRow4,officialRow5,officialRow6,officialRow7,officialRow8,officialRow9,officialRow10,officialRow11,officialRow12,officialRow13,officialRow14,officialRow15,officialRow16,officialRow17,officialRow18,officialRow19,officialRow20,officialRow21,officialRow22,officialRow23]

end Paper2.Certificates.Q6.Coverage
