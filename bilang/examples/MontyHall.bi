type door = {0, 1, 2}

join Host();
join Guest();
yield hidden Host(car: door);
yield Guest(d: door);
yield Host(goat: door) where goat != d;
yield Guest(switch: bool);
reveal car where goat != car;
if (car != undefined && switch != undefined) {
    var Winner: role = ((d != car) == switch) ? Guest : Host;
    transfer 20 from Host to Winner;
    transfer 20 from Guest to Winner;
}
if (car == undefined) transfer Host.value from Host to Guest;
if (switch == undefined) transfer Guest.value from Guest to Host;
