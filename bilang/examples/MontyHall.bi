type door = {0, 1, 2}

join Host;
join Guest;
yield hidden Host(car: door);
yield Guest(door: door);
yield Host(goat: door) where goat != door && goat != car;
yield Guest(switch: bool);
reveal car;
if (car == None || goat == None) {
    transfer Host.value from Host to Guest;
} else {
    var Winner: role = ((door != car) == switch) ? Guest : Host;
    transfer Host.value from Host to Winner;
    transfer Guest.value from Guest to Winner;
}
