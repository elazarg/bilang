type door = {0, 1, 2}

join Host();
join Guest();
yield Host(car: hidden door);
yield Guest(d: door);
yield Host(goat: door) where Host.goat != Guest.d;
yield Guest(switch: bool);
reveal Host(car: door) where Host.goat != Host.car;
return (Host.car != undefined && Guest.switch != undefined) ? { Guest -> ((Guest.d != Host.car) == Guest.switch) ? 20 : -20;  Host -> 0 }
     : (Host.car == undefined) ? { Guest -> 20;   Host -> -100 }
     : { Guest -> -100; Host -> 0 }
