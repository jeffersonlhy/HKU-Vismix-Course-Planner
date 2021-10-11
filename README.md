# HKU Vismix Planner  

HKU Vismix Planner is a set of python scripts that the Vismix backend invokes to compute all feasible timetables given the set of course schedules. The course schedule information is given to the program in a json file. This script is built upon Z3 solver where the course combination problem is treated as logical formulas expressed in first-order logic. 

## Getting Started

### Prerequisite

- [z3](https://github.com/Z3Prover/z3) is required. Install via pip as below,

```
pip install z3-solver
```

### Usage

```
python planner.py [semester] [total_courses] [comma_separated_courses] [path_to_courseJSON] 
```

Example

```
python planner.py Sem-2 5 COMP2396,COMP3322,COMP3234,COMP3270,MATH2101 course.json
```

The program reads a `course.json` for the course schedule information. This object can be generated by Vismix Schedule JSON Generator. 

### `course.json`
- Check `samples/course.json` for template of course.json.

```
    [{course}]

    course: {
        courseCode: String,
        courseName: String,
        timeDisplay: [time],
        slots: [{slot}]
    }

    time: {
        subClass: String,
        semester: String,
        Week 1: String
        Week 2: string
        Week 1 & 2: String
    }

    slot: {
        subClass: string,
        semester: String,
        venue: String,
        slots: [number]
    }

```

### Output
- For development purpose, logging level of `logger` is set as `DEBUG`. For production, logging level should be `INFO`.

- The script will return a json object as follow. This enables the python script to serve as a REST API where course requirement can be passed in the HTTP body.
```
    {
        status: String,
        timetables: [{timetable}],
        semester: String
    }

    timetable: {
        timetable: Integer, // the timetable number
        courses: [course],
        semester: String,
    }

    course: {
        course: String,
        subClass: String,
        slots: [Integer]
    }
```

### Example Output
```
2021-10-11 18:33:27,049 - DEBUG: Successful retrieved course info: COMP2396
2021-10-11 18:33:27,049 - DEBUG: Successful retrieved course info: COMP3322
2021-10-11 18:33:27,050 - DEBUG: Successful retrieved course info: COMP3234
2021-10-11 18:33:27,050 - DEBUG: Successful retrieved course info: COMP3270
2021-10-11 18:33:27,050 - DEBUG: Successful retrieved course info: MATH2101
2021-10-11 18:33:27,051 - DEBUG: Successful retrieved course info: MATH2012
2021-10-11 18:33:27,092 - DEBUG: Setting: 5 courses from ['COMP2396', 'COMP3322', 'COMP3234', 'COMP3270', 'MATH2101', 'MATH2012']
2021-10-11 18:33:27,093 - DEBUG: Result: 
2021-10-11 18:33:27,106 - DEBUG: Timetable: 1
2021-10-11 18:33:27,107 - DEBUG: COURSE: COMP2396, SUBCLASS: 2B
2021-10-11 18:33:27,108 - DEBUG: COURSE: COMP3322, SUBCLASS: 2B
2021-10-11 18:33:27,108 - DEBUG: COURSE: COMP3234, SUBCLASS: 2A/2B
2021-10-11 18:33:27,109 - DEBUG: COURSE: COMP3270, SUBCLASS: 2B
2021-10-11 18:33:27,109 - DEBUG: COURSE: MATH2012, SUBCLASS: 2B
2021-10-11 18:33:27,126 - DEBUG: Timetable: 2
2021-10-11 18:33:27,128 - DEBUG: COURSE: COMP2396, SUBCLASS: 2B
2021-10-11 18:33:27,128 - DEBUG: COURSE: COMP3322, SUBCLASS: 2B
2021-10-11 18:33:27,129 - DEBUG: COURSE: COMP3234, SUBCLASS: 2A/2B
2021-10-11 18:33:27,130 - DEBUG: COURSE: COMP3270, SUBCLASS: 2B
2021-10-11 18:33:27,130 - DEBUG: COURSE: MATH2101, SUBCLASS: 2B
2021-10-11 18:33:27,138 - DEBUG: Timetable: 3
2021-10-11 18:33:27,139 - DEBUG: COURSE: COMP2396, SUBCLASS: 2B
2021-10-11 18:33:27,140 - DEBUG: COURSE: COMP3322, SUBCLASS: 2B
2021-10-11 18:33:27,141 - DEBUG: COURSE: COMP3234, SUBCLASS: 2A/2B
2021-10-11 18:33:27,141 - DEBUG: COURSE: MATH2101, SUBCLASS: 2B
2021-10-11 18:33:27,142 - DEBUG: COURSE: MATH2012, SUBCLASS: 2B
2021-10-11 18:33:27,150 - DEBUG: Timetable: 4
2021-10-11 18:33:27,152 - DEBUG: COURSE: COMP2396, SUBCLASS: 2B
2021-10-11 18:33:27,152 - DEBUG: COURSE: COMP3322, SUBCLASS: 2B
2021-10-11 18:33:27,153 - DEBUG: COURSE: COMP3270, SUBCLASS: 2B
2021-10-11 18:33:27,153 - DEBUG: COURSE: MATH2101, SUBCLASS: 2B
2021-10-11 18:33:27,154 - DEBUG: COURSE: MATH2012, SUBCLASS: 2B
2021-10-11 18:33:27,168 - DEBUG: Timetable: 5
2021-10-11 18:33:27,169 - DEBUG: COURSE: COMP2396, SUBCLASS: 2B
2021-10-11 18:33:27,170 - DEBUG: COURSE: COMP3234, SUBCLASS: 2A/2B
2021-10-11 18:33:27,170 - DEBUG: COURSE: COMP3270, SUBCLASS: 2B
2021-10-11 18:33:27,171 - DEBUG: COURSE: MATH2101, SUBCLASS: 2B
2021-10-11 18:33:27,171 - DEBUG: COURSE: MATH2012, SUBCLASS: 2B
2021-10-11 18:33:27,181 - DEBUG: Timetable: 6
2021-10-11 18:33:27,182 - DEBUG: COURSE: COMP3322, SUBCLASS: 2B
2021-10-11 18:33:27,183 - DEBUG: COURSE: COMP3234, SUBCLASS: 2A/2B
2021-10-11 18:33:27,183 - DEBUG: COURSE: COMP3270, SUBCLASS: 2B
2021-10-11 18:33:27,184 - DEBUG: COURSE: MATH2101, SUBCLASS: 2B
2021-10-11 18:33:27,184 - DEBUG: COURSE: MATH2012, SUBCLASS: 2B
2021-10-11 18:33:27,191 - DEBUG: -- END --
```


