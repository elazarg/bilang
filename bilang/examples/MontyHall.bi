type door = {0, 1, 2}

join Host();
join Guest();
yield hidden Host(car: door);
yield Guest(d: door);
yield Host(goat: door) where goat != d;
yield Guest(switch: bool);
reveal car where goat != car;
if (car == undefined || goat == undefined) {
    transfer Host.value from Host to Guest;
} else {
    var Winner: role = ((d != car) == switch) ? Guest : Host;
    transfer Host.value from Host to Winner;
    transfer Guest.value from Guest to Winner;
}
