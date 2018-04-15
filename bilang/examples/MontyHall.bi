type door = {0, 1, 2}

receive join Host()
receive join Guest()
receive yield Host(car: hidden door)
receive yield Guest(d: door)
receive yield Host(goat: door) where Host.goat != Guest.d
receive yield Guest(switch: bool)
receive reveal Host(car: door) where Host.goat != Host.car
return (Host.car != undefined && Guest.switch != undefined)
? (
    ((Guest.d != Host.car) == Guest.switch)
    ? { Guest -> 20;  Host -> 0 }
    : { Guest -> -20; Host -> 0 }
) : (
    (Host.car == undefined)
    ? { Guest -> 20;   Host -> -100 }
    : { Guest -> -100; Host -> 0 }
)
