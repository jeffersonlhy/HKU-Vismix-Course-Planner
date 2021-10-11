import json
import sys, os
from z3 import *
import logging, logging.config


class ScheduleSolver():

    def __init__(self, numToTake, targetCourseCode, timelineSlots = 742):
        self.solver = Solver()
        self.numToTake = numToTake
        self.targetCourseCode = targetCourseCode
        self.allAvaCourses = []
        self.targetCoursesSchedule = []
        self.courseChoiceList = []
        self.subClassChoiceList = []
        self.masterTimeline = [BitVec(f"m_{i}", 16) for i in range(timelineSlots)]
        self.semester = ""
        self.debug = False
        logging.config.fileConfig(fname=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'config', 'logconfig.conf'), disable_existing_loggers=False)
        self.logger = logging.getLogger("development")


    def initSemester(self, sem):
        self.semester = sem

    def initAllCourse(self, pathToData):
        try:
            with open(pathToData) as outfile:
                self.allAvaCourses = json.load(outfile)
        except Exception as exp:
            self.logger.debug('Failed to read course schedule information.', exp)
            raise ValueError('Failed to read course schedule information.', exp)

    def initCourseChoiceList(self):
        self.courseChoiceList = [BitVec(f"c_{i}", 16) for i in range(self.numToTake)]

    def initSubclassChoiceList(self):
        for course in self.targetCoursesSchedule:
            # for courseCode, subClasses in course['slots']:
            courseCode = course['courseCode']
            self.subClassChoiceList.append(BitVec(f'{courseCode}_subClass', 16))

    def getCourseScheduleFromAllCourse(self, courseCode):
        course = next((course for course in self.allAvaCourses if courseCode in course['courseCode']), f"{courseCode}_NOT_FOUND")
        if "NOT_FOUND" not in course:
            course['slots'] = list(filter(lambda subClass: subClass['semester'] ==  self.semester, course['slots']))
            # What if the slots are blank
            self.logger.debug(f"Successful retrieved course info: {course['courseCode']}")
            return course
        else:
            raise ValueError("Course required by user does not exist in the schedule information.", course)
                
    def initTargetCourseSchedule(self):
        self.targetCoursesSchedule = [self.getCourseScheduleFromAllCourse(code) for code in self.targetCourseCode]
        
    def addCourseChoiceSortedConstraint(self):
        self.solver.add([self.courseChoiceList[i] < self.courseChoiceList[i+1] for i in range(self.numToTake - 1)])
        self.solver.add([self.courseChoiceList[i] >= 0 for i in range(self.numToTake)])
        self.solver.add([self.courseChoiceList[i] < len(self.targetCourseCode) for i in range(self.numToTake)])

    def addTimeClashConstraint(self):
        for i in range(len(self.targetCoursesSchedule)):
            courseConstraint = [] # store all the constraint per course
            course = self.targetCoursesSchedule[i]
            if course == "NOT_FOUND":
                continue
            isSelected = Or([self.courseChoiceList[j] == i for j in range(self.numToTake)])
            subClasses = course['slots']
            numOfSubclass = len(subClasses)
            subClassChoice = self.subClassChoiceList[i]
            courseConstraint.append(Implies(isSelected, And(subClassChoice >= 0, subClassChoice < numOfSubclass)))
            courseConstraint.append(Implies(Not(isSelected), subClassChoice == -1))
            for subClassIdx, subClass in enumerate(subClasses):
                slotSelected = (subClassChoice == subClassIdx)
                for slot in subClass['slots']:
                    uniqueNumber = 10 + i
                    slotConstraint = Implies(slotSelected, self.masterTimeline[slot] == uniqueNumber)
                    courseConstraint.append(slotConstraint)
            self.solver.add(courseConstraint)

    def addRepeatConstraint(self, model):
        repeatConstraint = []
        for courseChoice in self.courseChoiceList:
            repeatConstraint.append(courseChoice != model[courseChoice])
        for subClassChoice in self.subClassChoiceList:
            repeatConstraint.append(subClassChoice != model[subClassChoice])
        self.solver.add(Or(repeatConstraint))

    def getAllTimetable(self):
        timetableList = []
        timetableNum = 1
        if self.solver.check() == sat:
            self.logger.debug(f"Setting: {self.numToTake} courses from {self.targetCourseCode}")
            self.logger.debug(f"Result: ")
            while (self.solver.check() == sat):
                timetable = {
                    'timetable': timetableNum,
                    'courses': [],
                    'semester': self.semester
                }
                self.logger.debug(f"Timetable: {timetableNum}")
                m = self.solver.model()
                for courseIdx, choice in enumerate(self.courseChoiceList):
                    courseChoice = m[choice].as_long() # 2 = second course
                    subClassChoiceIdx = m[self.subClassChoiceList[courseChoice]].as_long()
                    courseCode = self.targetCourseCode[courseChoice]
                    subClass = self.targetCoursesSchedule[courseChoice]['slots'][subClassChoiceIdx]['subClass']
                    slots = self.targetCoursesSchedule[courseChoice]['slots'][subClassChoiceIdx]['slots']
                    self.logger.debug (f"COURSE: {courseCode}, SUBCLASS: {subClass}")
                    timetable['courses'].append({
                        'course': courseCode,
                        'subClass': subClass,
                        'slots': slots
                    })
                timetableList.append(timetable)
                self.addRepeatConstraint(m)
                timetableNum += 1
            self.logger.debug ("-- END --")
            return timetableList
        else:
            self.logger.debug("No satisfiable timetable can be found.")
            return []

    def sortTimetable(self, timetable):
        # timetable.sort(lambda x,y : cmp(x['name'], y['name']))
        # timetable = sorted(timetable, key=lambda k: k['name'])
        for t in timetable:
            r = sorted(t['courses'], key=lambda k: k['course'])
        return timetable

    def getCourseIndex(self, course):
        for idx, item in enumerate(self.targetCourseCode):
            if item == course:
                return idx
        else:
            return 1 # prevent Error

    def getIndexTimetable(self, timetable):
        for t in timetable:
            for courses in t['courses']:
                courses['index'] = self.getCourseIndex(courses['course'])
        return timetable

    def debugPrint(self, str):
        if self.debug:
            self.debugPrint(str)

if __name__ == "__main__":
    try:
        semester = sys.argv[1].replace('-', ' ')
        courseToTake = int(sys.argv[2])
        courseTargeted = sys.argv[3].split(',')
        pathToData = sys.argv[4]
    except Exception as e:
        print ("Internal Error", e)
        sys.exit(0)

    try:
        solver = ScheduleSolver(courseToTake, courseTargeted)
        solver.initSemester(semester)
        solver.initAllCourse(pathToData)
        solver.initCourseChoiceList()
        solver.initTargetCourseSchedule()
        solver.initSubclassChoiceList()
        solver.addCourseChoiceSortedConstraint()
        solver.addTimeClashConstraint()
        timetable = solver.getAllTimetable()
        sortedTimetable = solver.getIndexTimetable(timetable)
        status = 'Success' if len(timetable) > 0 else 'No timetable found'
        print (json.dumps({
            'status': status,
            'timetables': sortedTimetable
        }))
    except Exception as e:
        print (json.dumps({
            'status': 'Calculation Error',
            'courseSetup': f'{courseTargeted}',
            'details': str(e),
        }))

# Usage: python schedulePlanner.py Sem-1 5 'COMP2396,COMP3322,COMP3234,COMP3270,MATH2101'
