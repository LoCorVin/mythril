from time import clock
first_time=None
meassure=False
last_time = None

def start_meassure():
    if meassure:
        global last_time
        global first_time
        last_time = clock()
        if not first_time:
            first_time=last_time

def printt(title):
    if meassure:
        global last_time
        print(title + ": " + str(clock() - last_time))
        last_time = clock()

def printend():
    if meassure:
        print("END: " + str(clock() - first_time))
