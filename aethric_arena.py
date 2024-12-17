#!/usr/bin/python
# Import required packages
import cv2 as cv
import cv2 as cv2
import pytesseract
import sys
import optparse
import subprocess
import os
import time
import threading
import queue
import signal
import re
from pathlib import Path
import numpy as np
import math
import inspect #pass frame to sig handler
from skimage.feature import hog
import imutils
from imutils.object_detection import non_max_suppression
from PyQt5 import QtGui
from PyQt5 import QtCore
#from PyQt5.QtWidgets import QWidget, QApplication, QLabel, QVBoxLayout, QTable, QTableItem
from PyQt5.QtWidgets import * 
from PyQt5.QtGui import QPixmap
from PyQt5.QtCore import *
#pyqtSignal, pyqtSlot, Qt, QThread
import json
import webbrowser
import requests
import urllib
from ppretty import ppretty
import traceback

#
page = 1

# Adaptive threshold levels
BKG_THRESH = 30
CARD_THRESH = 30
SERIAL = ""


#  Code derived and adapted from optical character recognition based playing card software that I wrote 
#   in order to aid in managing and trading tangible collectible cards
#

BUTTON_TEXT='EXIT'

BUTTONS = { 'EXIT': 'tap', 'CONTINUE': 'tap', 'HOLD TO SPAR': 'hold', 'HOLD SPAR': "hold", 'HOLD TO BATTLE': 'hold', 'HOLD BATTLE': 'hold', 'HOLD TO BATTLE.':'hold', 'CONTINUE': 'tap'}
#BUTTON_TEXT='HOLD TO SPAR'

#"self.tap(961,1110)","self.tap(1200,980)"]
#this is on 7 spells
BTNCOORDS = { 1: (260,860), 2: (950,860), 3: (1200, 860), 4: (1656, 860), 5:(260, 966), 6:(720, 966), 7:(1673,966),
        20: (1200,980), 21:(961,1110), 22: (500,500), 23: (500,500) 
        }

#9 spells
BTNCOORDS = { 1: (260,750), 2: (950,750), 3: (1200, 750), 4: (1656, 750), 5:(260, 860), 6:(720, 860), 
        7: {1200, 860}, 8:(1673,860), 9:(500,500),
        20: (960,1100), #(X)
        21:(1200,975),  #Offhand
        22: (1400,1100), #Item
        49: (1180,650), #19th item (currently large mana) of 31
        23: (270, 850), #potion
        24: (500,500) 
        }

BTNCOORDS = { 1: (260,750), 2: (950,750), 3: (1200, 750), 4: (1656, 750), 
        5:(260, 860), 6:(720, 860), 7: {1200, 860}, 8:(1673,860), 
        9:(260,960), 10:(720,960), 11:(1673,960),
        20: (960,1100), #(X)
        21:(1200,975),  #Offhand
        22: (1400,1100), #Item
        49: (1180,650), #19th item (currently large mana) of 31
        23: (270, 850), #potion
        24: (500,500) 
        }



BTNMAP = {
'Arena': { "summon": 3, "ward": 5, "heal": 4, "mend": 7, "stun": 10, "freeze": 9, "blind": 8, "offhand": [20,21] },
'Raid': { "summon": {"n":1, "t":2}, "mimic": 2, "mend": 4, "ward": 5, "heal": 7, "offhand": [20,21], "potion": [20,23], "set potion 19": [20,22,49], "greater elixir":[20,21,23] },
}
            #2nd of 7 spells (or of 8
#            self.tap(950,860)

            #3rd of 7 spells (or of 8
#            self.tap(1200,860)

            #4th of 7 spells (or of 8
#            self.tap(1656,860)

            #5th of 7 spells (or 5th of 8)
#            self.tap(260,966)

            #6th of 7 spells (or 6th of 8)
#            self.tap(720,966)

            #7th of 7 spells (or 8th of 8
#            self.tap(1673,966)



def stdout_reader(proc, q):
    for line in iter(proc.stdout.readline, b''):
        q.put(line.decode('utf-8'))

def stderr_reader(proc, q):
    for line in iter(proc.stderr.readline, b''):
        q.put(line.decode('utf-8'))

def handler(signum, frame):
    try:
        if (isinstance(proc, subprocess.Popen)):
            proc.terminate()
        sys.exit(app.exec_())
    except:
        pass
    sys.exit()

def nothing(*arg):
    pass

class Actions(object):
    def __init__(self, *args, **kwargs):
        self.debug = 0
        if 'debug' in kwargs:
            self.debug = kwargs['debug']
        if self.debug > 3:
            print("Actions __init begin")
        self.currentAction = None
        self.currentActionStart = None
        self.waitForStart = None
        self.waitForEnd = None
        self.currentActionEnd = None
        self.timeout = 5
        self._scale = None
        self._device_width = None
        self._device_height = None
        self._X11_width = None
        self._X11_height = None
        self._mOption = None
        self._serial = None
        self.iActions = []
        self.cActions = []
        if 'serial' in kwargs:
            self._serial = kwargs['serial']
        if self.debug > 3:
            print("Actions __init end")

    #  ms
    def clock(self):
        return (cv.getTickCount() / cv.getTickFrequency()) * 1000

    def actions(self,Pactions=[]):
        if hasattr(Pactions,'__len__'):
            if len(Pactions) == 0:
                raise Exception("derive this class and override this method to provide a default action list")
            else:
                if (not self.iActions):
                    self.iActions = Pactions
                    self.cActions  = self.iActions
        else:
            raise Exception("invalid parameter to actions")

        return self.cActions

    def nextAction(self):
        actions = self.actions()
        if not len(actions):
            self.reset()
            actions = self.actions()

        self.currentAction = actions.pop(0)
        self.currentActionStart = None
        self.currentActionEnd = None
        return self.currentAction

    def action(self, Paction=[]):
        if (self.currentAction == None):
            self.nextAction()
        return self.currentAction

    def do(self):
        action = self.action()
        if self.currentActionStart == None or self.currentActionEnd == None:
            self.currentAction = None
            self.currentActionStart = self.clock()

        # only waitFor action can set waitForStart
            if self.waitForStart == None:
                if isinstance(action, dict):
                    if self.debug > -1:
                        print("do: %s - %s" % (action["name"], action["action"]))
                else:
                    if self.debug > -1:
                        print("self.currentAction: [%s]" % action)

            if isinstance(action, dict):
                exec(action["action"])
            else:
                exec(action)

        else:
            print("do(): doing nothing, action started at [%s]" % self.currentActionStart)
            raise Exception("action apparently did not handle start & end properly")

    def getResolutions(self):
        try:
            serial = self.serial()
        except:
            return (None, None, None, None)

    #  get android device physical size
        cmd = "adb -s %s shell wm size" % serial
        result = subprocess.run(cmd.split(), capture_output=True, text=True)
        x = 0
        y = 0
        X11x = 0
        X11y = 0
        
        if (len(result.stdout) > 0):
            m = re.search(r"^(Physical size: )(?P<y>\d+)x(?P<x>\d+)\s", result.stdout, re.M)
            x = str(m.group('x'))
            y = str(m.group('y'))

    #get X11 resolution
        cmd = "xrandr --current"
    # | grep '*' | uniq | awk '{print $1}' | cut -d 'x' -f1"
        result = subprocess.run(cmd.split(), capture_output=True, text=True)
        if (len(result.stdout) > 0):
            m = re.search(r".*?(?P<x>\d+)x(?P<y>\d+)\s+.*?\*", result.stdout, re.M)
            X11x = str(m.group('x'))
            X11y = str(m.group('y'))

        if self.debug > -1:
            print("device %s has resolution (%s,%s), X11 has resolution (%s, %s)" % (serial,x,y,X11x,X11y))
        self._device_width = x
        self._device_height = y
        self._X11_width = X11x
        self._X11_height = X11y
        return (x,y,X11x,X11y)

    def resolutions(self):
        if (self._device_width == None or self._device_height == None or self._X11_width == None or self._X11_height == None):
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return (self._device_width,self._device_height,self._X11_width,self._X11_height)

    def device_width(self):
        if (self._device_width == None):
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return self._device_width

    def device_height(self):
        if (self._device_height == None):
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return self._device_height
    def X11_width(self):
        if (self._X11_width == None):
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return self._X11_width

    def X11_height(self):
        if (self._X11_height == None):
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return self._X11_height

    def scale(self):
        (device_width,device_height,X11_width,X11_height) = self.resolutions()
        if ((device_width > X11_width) or (device_height > X11_height)):
            self._scale=0.5
        else:
            self._scale = 1

        return self._scale

    #  option that will be used to start video for linux
    #
    def mOption(self):
        if (self._mOption == None):
            print(self.device_width())
            print(self.scale())
            self._mOption = int(float(self.device_width()) * float(self.scale()))
        return self._mOption

    def serial(self):
        if (not self._serial):
#len(self._serial) <= 0):
            self.getDeviceSerial()
        return self._serial

    def getDeviceSerial(self,Pserial=""):
        if (len(Pserial)):
            self._serial = Pserial
        try:
            self._serial = os.environ['ANDROID_SERIAL']
        except:
            pass

        cmd = "adb devices"
        result = subprocess.run(cmd.split(), capture_output=True, text=True)
        
        if (len(result.stdout) > 0):
            m = re.search(r"^(?!(List|\s+))(?P<serial>.*?)\s", result.stdout, re.M)
            if m:
                if (self._serial):
                    if (str(m.group('serial')) == self._serial):
                        if self.debug > -1:
                            print("using connected device [%s]" % self.serial)
                        return self._serial
                else:
                    self._serial = str(m.group('serial'))
                    if self.debug > -1:
                        print("using connected device [%s]" % self._serial)
                    return self._serial
        raise Exception("no connected android device!") 

#  high level actions begin here
#
    def tap(self, x,y):
        cmd = "adb -s %s shell input tap %s %s" % (self.serial(),x / self.scale(),y / self.scale())
        if self.debug > 1:
            print(cmd)
        result = subprocess.run(cmd.split(), capture_output=True, text=True)
        self.currentActionEnd = self.clock()
        if self.debug > 2:
            print(result)
        return result

    def hold(self, x,y, seconds):
        cmd = "adb -s %s shell input swipe %s %s %s %s %s" % (self.serial(),x / self.scale(),y / self.scale(), x / self.scale(), y / self.scale(), seconds * 1000)
        if self.debug > 1:
            print(cmd)
        result = subprocess.run(cmd.split(), capture_output=True, text=True)
        self.currentActionEnd = self.clock()
        if self.debug > 2:
            print(result)
        return result

    def waitFor(self, seconds):
        #print("%s.waitFor(%s)"%(type(self), seconds))

        #re-entrant version
        if self.waitForStart:
            delta = self.clock() - self.waitForStart
           # print("delta: [%s]" % delta)
            if delta >= (seconds * 1000):
                self.currentAction = None
                self.currentActionEnd = self.clock()
                self.waitForStart = None
                print("action is ending, actual wait time was %s ms" % delta)
            else:
            #    print("action is ongoing, setting currentAction")
                self.currentAction = "self.waitFor(%s)" % (seconds)
        else:
            self.currentAction = "self.waitFor(%s)" % (seconds)
            self.waitForStart = self.currentActionStart

            #once set, let do() handle clearing
            self.waitForEnd = self.waitForStart + (seconds * 1000)
            #if self.waitForStart == None:
            #raise Exception("method not called with %s.do()" % type(self))

    def reset(self):
        if self.debug > 0:
            print("Actions.reset")
        self.waitForStart = None
        self.cActions = self.iActions
        self.currentAction = None
        self.currentActionStart = None
        self.currentActionEnd = None

class Aethric(Actions):
    def __init__(self, *args, **kwargs):
        super(Aethric, self).__init__(*args, **kwargs)
        if self.debug > 3:
            print("Aethic __init end")
        self.Arena = ["summon", "ward", "summon", "stun", "freeze", "mend", "ward", "summon"]
        self.Raid = ["ward", "summon", "offhand", "summon", "summon", "offhand", "summon", "mend", "summon", "offhand", "mend", "mend", "offhand", "mend", "mend", "offhand", "mend", "mend","offhand", "mend", "heal", "offhand"]
        self.RaidHard = ["summon", "mend", "offhand", "summon", "mend", "offhand", "mend", "mend", "heal", "offhand", "mend", "mend", "heal", "offhand", "mend", "mend","heal", "offhand", "offhand", "offhand"]
        self.RaidQ = ["summon", "offhand", "offhand", "mend", "potion"]
        self.RaidHard2 = ["ward","summon","mend","offhand","mend","mend","offhand", "heal"]
        self.RaidHard3 = ["ward","summon","mend","offhand","mend","mend","offhand", "summon", "offhand", "potion", "potion"]
        self.mode = "Arena"
        self.Raid = self.RaidHard3

        if "mode" in kwargs:
            if hasattr(self,kwargs["mode"]):
                self.mode = kwargs["mode"]
        self.modeSteps = getattr(self,self.mode)
        self.names = []
        self.sleep = 8
        if self.debug > 3:
            print("Aethic __init end")

    def actions(self, actions=[]):
        if hasattr(actions, "__len__"):
            # get
            if (len(actions) == 0):
                #initialize
                if not self.iActions:
#                    self.iActions = self.make_button_taps(["summon", "summon", "ward", "summon", "heal", "summon", "buff", "debuff", "ward", "summon", "offhand"])
                    self.iActions = self.make_button_taps(self.modeSteps)
                    print(self.mode)
                    print(self.modeSteps)
                    print(self.iActions)
                    #let reset() handle this, otherwise when event loop calls do() it will begin
                    #self.cActions = self.iActions
            # set
            else:
                print("len of parameter to actions is %s" % len(actions))
                raise Exception("please use constructor for setting default actions")
        else:
            raise Exception("implement me. %s.actions() passed a %s, val [%s]" % (type(self), type(actions), actions))
        return self.cActions

    def disable_scale(self):
        self.scale_disabled = 1

    def enable_scale(self):
        self.scale_disabled = 0

    def scale(self):
        if hasattr(self, "scale_disabled") and self.scale_disabled:
            return 1
        return super(Aethric, self).scale()

    def do(self):
        #doesn't work
        self.disable_scale()
        super(Aethric,self).do()
        self.enable_scale()

    def make_button_taps(self,maptokens):
        taps = []
        bmap = BTNMAP[self.mode]
        self.names = []
        for t in maptokens:
            if t in bmap:
                el = bmap[t]
            else:
                raise Exception("BTNMAP[%s] missing token %s" % (self.mode,t))

            seq = []
            turn = []

            # if its a list, its a sequence of buttons
            if hasattr(el, "__len__"):
                seq = el
                #  apparently dict's have a __len__ attr
                if isinstance(el, dict):
                    seq = [el]
            else:
                seq = [el]

            s = self.sleep
            for n in seq:
                if isinstance(n, dict): #{'n': [button_number], 't': [turns]}
                    bn = n["n"]
                    s = (n["t"] * (self.sleep - 1))
                else:
                    bn = n

                if bn not in BTNCOORDS:
                    raise Exception("BTNCOORDS missing %s" % (bn))
                (x,y) = BTNCOORDS[bn]
                turn.append("self.tap(%s,%s)" % (x,y))
                turn.append("self.waitFor(%s)" % 1)
                s -= 1

            turn.append("self.waitFor(%s)" % s)

            i = 1
            for el in turn:
                name = "%s[%s]" % (t, i)
                i+= 1
                taps.append({"action":el, "name":name})
        return taps

def rectContains(rect,pt):
    logic = rect[0] < pt[0] < rect[0]+rect[2] and rect[1] < pt[1] < rect[1]+rect[3]
    return logic

class VideoThread(QThread):
    change_pixmap_signal = pyqtSignal(np.ndarray)
    change_text_signal = pyqtSignal(dict)
    canny_lower_signal = pyqtSignal(int)
    canny_upper_signal = pyqtSignal(int)
    thresh_lower_signal = pyqtSignal(int)
    thresh_upper_signal = pyqtSignal(int)

    def __init__(self,vdev=0,lower=None, upper=None, lowerT=None, upperT=None,debug=False, actions=None):
        super().__init__()
        self._run_flag = True
        self.previous_frame = None #motion detection
        self.frame_count = 0
        self.vdev = vdev
        self.timeout = 5
        self.cardsByTile = {}
        self.show_tile_grid = False
        self.scale_percent = 100 # percent of original size
        if (actions):
            self.actions = actions
        else:
            self.actions = Actions()
        #self.scale = self.actions.scale()
        #self.device_width = int(self.actions.device_width())
        #self.device_height = int(self.actions.device_height())
        self.method="edge"
        self.debug = debug
        self.debug = 3
        self.image_options = None
        self.mode_options = None
        self.cannyLower = lower
        self.cannyUpper = upper
        self.threshLower = lowerT
        self.threshUpper = upperT
        self.frames = []
        self.motion = []
        self.motionFrames = 10
        self.framesMax = 10
        self.spell_menu = False
        self.ward_turns = 0
        self.health_percent = 0
        self.mana_percent = 0
        self.ward_percent = 0
        self.summons = 0
        self.sawSummonsAt = [0,0,0,0,0]
        self.spriteMoveTime = 4
        self.xbtn_template = cv.imread('aethric/x_btn_black_10px_border.png', 0)
        # load the pre-trained EAST text detector
        print("[INFO] loading EAST text detector...")
        self.net = cv.dnn.readNet("frozen_east_text_detection.pb")



    def fast_east(self,image,min_confidence=0.5):
        orig = image.copy()
        (H, W) = image.shape[:2]

        # set the new width and height and then determine the ratio in change
        # for both the width and height
        (newW, newH) = (224, 64)
        rW = W / float(newW)
        rH = H / float(newH)

        # resize the image and grab the new image dimensions
        image = cv.resize(image, (newW, newH))
        (H, W) = image.shape[:2]

        # define the two output layer names for the EAST detector model that
        # we are interested -- the first is the output probabilities and the
        # second can be used to derive the bounding box coordinates of text
        layerNames = [
            "feature_fusion/Conv_7/Sigmoid",
            "feature_fusion/concat_3"]

        # construct a blob from the image and then perform a forward pass of
        # the model to obtain the two output layer sets
        blob = cv.dnn.blobFromImage(image, 1.0, (W, H),
            (123.68, 116.78, 103.94), swapRB=True, crop=False)
        start = time.time()
        self.net.setInput(blob)
        (scores, geometry) = self.net.forward(layerNames)
        end = time.time()

        # show timing information on text prediction
    #    print("[INFO] text detection took {:.6f} seconds".format(end - start))

        # grab the number of rows and columns from the scores volume, then
        # initialize our set of bounding box rectangles and corresponding
        # confidence scores
        (numRows, numCols) = scores.shape[2:4]
        rects = []
        confidences = []

        # loop over the number of rows
        for y in range(0, numRows):
            # extract the scores (probabilities), followed by the geometrical
            # data used to derive potential bounding box coordinates that
            # surround text
            scoresData = scores[0, 0, y]
            xData0 = geometry[0, 0, y]
            xData1 = geometry[0, 1, y]
            xData2 = geometry[0, 2, y]
            xData3 = geometry[0, 3, y]
            anglesData = geometry[0, 4, y]

            # loop over the number of columns
            for x in range(0, numCols):
                # if our score does not have sufficient probability, ignore it
                if scoresData[x] < min_confidence:
                    continue

                # compute the offset factor as our resulting feature maps will
                # be 4x smaller than the input image
                (offsetX, offsetY) = (x * 4.0, y * 4.0)

                # extract the rotation angle for the prediction and then
                # compute the sin and cosine
                angle = anglesData[x]
                cos = np.cos(angle)
                sin = np.sin(angle)

                # use the geometry volume to derive the width and height of
                # the bounding box
                h = xData0[x] + xData2[x]
                w = xData1[x] + xData3[x]

                # compute both the starting and ending (x, y)-coordinates for
                # the text prediction bounding box
                endX = int(offsetX + (cos * xData1[x]) + (sin * xData2[x])) 
                endY = int(offsetY - (sin * xData1[x]) + (cos * xData2[x]))
                startX = int(endX - w)
                startY = int(endY - h)

                # scale the bounding box coordinates based on the respective
                # ratios
                #startX = int(startX * rW)
                #startY = int(startY * rH)
                #endX = int(endX * rW) + 2
                #endY = int(endY * rH) + 2

                # add the bounding box coordinates and probability score to
                # our respective lists
                rects.append((startX, startY, endX, endY))
                confidences.append(scoresData[x])

        # apply non-maxima suppression to suppress weak, overlapping bounding
        # boxes
        boxes = non_max_suppression(np.array(rects), probs=confidences)

        rects = []
        for (startX, startY, endX, endY) in boxes:
            # scale the bounding box coordinates based on the respective
            # ratios
            startX = int(startX * rW)
            startY = int(startY * rH)
            endX = int(endX * rW) + 2
            endY = int(endY * rH) + 2

            rects.append((startX, startY, endX, endY))

        return rects

    def angle_cos(self,p0, p1, p2):
        d1, d2 = (p0-p1).astype('float'), (p2-p1).astype('float')
        return abs( np.dot(d1, d2) / np.sqrt( np.dot(d1, d1)*np.dot(d2, d2) ) )

    def tess(self, img,whitelist=""):
        words = []
        chars= "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+-_."
        if len(whitelist) > 0:
            chars = whitelist
        tconf = "--oem 3 --psm 8 "+ \
            "-c tessedit_char_whitelist=\"%s\"" % chars
        
        try:
            text = pytesseract.image_to_data(img, config=tconf, output_type='data.frame')
            text = text[text.conf != -1]
            print(text)
#                                    print()
            try:
                #level,page_num,block_num,par_num,line_num,word_num,left,top,width,height,conf,text        
                lines = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['text'].apply(lambda x: x.values.tolist()).tolist()
                confs = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['conf'].mean().tolist()
            
                tl = []
                tc = []
                for i in range(len(lines[0])):
                    if str(lines[0][i]).strip():
                        tl.append(str(lines[0][i]))

                line = " ".join(tl)  #more likely multiple words, but still can be single word
#                        print(line)

                conf = 0
                if (np.any(confs)):
                    conf = round(np.mean(confs),2)
                    print(conf)
                if (conf >= 10):
                    words.append(line)

            except BaseException as err:
                print(f"Unexpected {err=}, {type(err)=}")
                print(text)
        except BaseException as err:
            print(f"Unexpected {err=}, {type(err)=}")

        return words

    def find_squares(self, img, thresh=None):
        if thresh is None:
            # denoise before edge detection
            blur = cv.GaussianBlur(img,(5,5),0)

            #  normalize color histogram for greater contrast
            #
    #  returns cb []
    #      center coords of bounding box which fast_east algo returns
    #  words []
    #    the words tesseract read inside that box with a 50% confidence or above
    
    def fast_east_tess(self, image):
        cb = []
        words = []
        boxes = self.fast_east(image)

        boxc = 0
        for box in sorted(boxes, key=lambda x: x[0]):
            boxc += 1
           
            (x, y, x2, y2) = box
#                x, y, w, h = unscaled
                #crop
 #               cardimage=orig[y: y + h, x : x + w]
            print("x[%d] y[%d] x2[%d] y2[%d]" % (x,y,x2,y2))
            img = image[y:y2,x:x2]

#            if (img is None):
#                print("Empty!")
#            print(box, boxc,"cards/%d_%d_%d_%d.title.%d.png" % (tile[0], tile[1], tile[2], tile[3], boxc))
#            print(type(img))
            
            # draw the bounding box on the image
#            cv.rectangle(im2, (x, y), (x2, y2), (0, 255, 0, 1))

            tconf = "--oem 3 --psm 7 "+ \
                "-c tessedit_char_whitelist=\"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+-_.\""
            
            try:
                text = pytesseract.image_to_data(img, config=tconf, output_type='data.frame')
                text = text[text.conf != -1]
#                                    print()
                print(text)
                try:
                    #level,page_num,block_num,par_num,line_num,word_num,left,top,width,height,conf,text        
                    lines = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['text'].apply(lambda x: x.values.tolist()).tolist()
                    confs = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['conf'].mean().tolist()
                
                    tl = []
                    tc = []
                    for i in range(len(lines[0])):
                        if str(lines[0][i]).strip():
                            tl.append(str(lines[0][i]))

                    line = " ".join(tl)  #more likely multiple words, but still can be single word
#                        print(line)

                    conf = 0
                    if (np.any(confs)):
                        conf = round(np.mean(confs),2)
#                        print(conf)
                    if (conf > 50):
                        words.append(line)
                        cb.append((x+(x2-x)/2,y+(y2-y)/2))

                except BaseException as err:
                    print(f"Unexpected {err=}, {type(err)=}")
                    print(text)
            except BaseException as err:
                print(f"Unexpected {err=}, {type(err)=}")
        return (cb, words)
#        return (cb, words)

    def find_squares(self, img, thresh=None):
        if thresh is None:
            # denoise before edge detection
            blur = cv.GaussianBlur(img,(5,5),0)

            #  normalize color histogram for greater contrast
            #
            clahe = cv.createCLAHE(clipLimit=2.0, tileGridSize=(8,8))
            contrast = clahe.apply(img)

            median_pix = np.median(img)
            if (self.cannyLower is None):
                self.cannyLower = int(max(0 ,0.7*median_pix))
                self.canny_lower_signal.emit(self.cannyLower)

            if (self.cannyUpper is None):
                self.cannyUpper = int(min(255,1.3*median_pix))
                self.canny_upper_signal.emit(self.cannyUpper)

    #        print(median_pix, self.cannyLower, self.cannyUpper)

            edge = cv.Canny(contrast, self.cannyLower, self.cannyUpper)#, apertureSize=5)
        else:
            edge = thresh

        if (self.image_options == "Edge C"):
            im3 = img.copy()
            contours, hierarchy = cv.findContours(edge, 
                cv.RETR_LIST, cv.CHAIN_APPROX_SIMPLE)

            for i in range(len(contours)):
                cv.drawContours(im3, contours, i, (255, 0, 0), \
                                1, cv.LINE_8, hierarchy, 0)
            self.change_pixmap_signal.emit(im3)

        # dilate canny output to remove potential
        # holes between edge segments
        rect_kernel = cv.getStructuringElement(cv.MORPH_RECT, (1, 8))
#               edge = cv.erode(edge, rect_kernel, iterations=1)
        edge = cv.dilate(edge, rect_kernel, iterations=1)
        rect_kernel = cv.getStructuringElement(cv.MORPH_RECT, (8, 1))
#               edge = cv.erode(edge, rect_kernel, iterations=1)
        edge = cv.dilate(edge, rect_kernel, iterations=1)

        #im2 = np.uint8(im2/2.)
        #im2[edge != 0] = (0,255,0)
        contours, hierarchy = cv.findContours(edge, 
            cv.RETR_LIST, cv.CHAIN_APPROX_SIMPLE)

        if (self.image_options == "Sq Edge"):
            self.change_pixmap_signal.emit(edge)
        elif (self.image_options == "Sq Edge Contours"):
            im3 = img.copy()
            for i in range(len(contours)):
                cv.drawContours(im3, contours, i, (255, 0, 0), \
                                2, cv.LINE_8, hierarchy, 0)
            self.change_pixmap_signal.emit(im3)

        rect=[]
        for cnt in contours:
            approx = cv.approxPolyDP(cnt,0.02*cv.arcLength(cnt,True),True)
            if (len(approx)==4 and abs(cv.contourArea(cnt)) > (self.tileW * self.tileH)):
                #and abs(cv.contourArea(cnt)) <  ):
#                        print(abs(cv.contourArea(cnt)))
                cnt = approx.reshape(-1, 2)
                max_cos = np.max([self.angle_cos( cnt[i], cnt[(i+1) % 4], cnt[(i+2) % 4] ) for i in range(4)])
                if max_cos < 0.1:
                    rect.append(cnt)
        return rect

    def read_percent_bar(self,image, mask):
        width = image.shape[1] - 1
        height = image.shape[0] - 1 

        cv.imwrite("mana_bgr.png", image)
        hsv = cv2.cvtColor(image, cv2.COLOR_BGR2HSV)
        cv.imwrite("mana_hsv.png", hsv)

#        print("B median %s range %s std %s" % (np.median(image,axis=0),np.ptp(image,axis=0),np.std(image,axis=0)))
#        print("G median %s range %s std %s" % (np.median(image,axis=1),np.ptp(image,axis=1),np.std(image,axis=1)))
#        print("R median %s range %s std %s" % (np.median(image,axis=2),np.ptp(image,axis=2),np.std(image,axis=2)))
#        norm = cv2.normalize(image, None, 0, 1.0, cv2.NORM_MINMAX, dtype=cv2.CV_32F)
#       rounded = np.round(norm, 1)
 #       print(norm)
#        mean, std = cv2.meanStdDev(image)
#        print("mean: %s stddev: %s" % (np.squeeze(mean), np.squeeze(std)))

#        black = cv2.inRange(image, np.array([0, 0, 0]), np.array([180,255,30]))
        #black = cv2.inRange(image, np.array([0, 0, 130]), np.array([100,20,170]))
#        black = cv2.inRange(image, np.array([0, 0, 0]), np.array([255,35,110]))
#        blue = cv2.inRange(image, np.array([200, 35, 60]), np.array([230,105,110]))
#        blue = cv2.inRange(hsv, np.array([50, 35, 20]), np.array([110,105,85]))
#        blue = cv2.inRange(hsv, np.array([110,50,50]), np.array([130,255,255]))
#        blue = cv2.inRange(hsv, np.array([20, 35, 50]), np.array([85,105,110]))
        masks = {}
        masks['blue'] = cv2.inRange(hsv, np.array([100, 50, 50]), np.array([120,255,255]))
        red_low = cv2.inRange(hsv, np.array([0, 90, 20]), np.array([10,255,255]))
        red_high = cv2.inRange(hsv, np.array([175, 90, 20]), np.array([185,255,255]))
        masks['red'] = red_low + red_high
        masks['purple'] = cv2.inRange(hsv, np.array([120, 50, 50]), np.array([140,255,255]))

        
        masked = cv2.bitwise_and(image,image, mask = masks[mask])

#display the masked image

#        print(masked.shape)

#        print(image)
#        print(masked)
        return np.count_nonzero(np.sum(np.sum(masked,0),1) > 0) / masked.shape[1] * 100



    def run(self):
#if 'size' in params:
#    w, h = map(int, params['size'].split('x'))
#vid.set(cv.CAP_PROP_FRAME_WIDTH, 2400)
#vid.set(cv.CAP_PROP_FRAME_HEIGHT, 1080)

        cap = cv.VideoCapture(self.vdev)
        waited=0
        feedback = ""
        while self._run_flag:
            _ret, orig = cap.read()
            if (orig is None):
                time.sleep(0.1) 
                waited=waited+0.1
                if (waited > self.timeout):
                    cap = cv.VideoCapture(self.vdev)
                    waited=0
                continue
            else:
                self.frame_count += 1

        #    if ((frame_count % 2) != 0):
        #        continue

            #  classically OCR uses white as text foreground and black for background
            #  
            #  MTG typically has black text on a lighter color bg
            #
        #    print('Original Dimensions : ',img.shape)
            self.prev_scale = self.scale_percent
#            scale_percent = cv.getTrackbarPos('scale', 'edge')
            self.width = orig.shape[1]
            self.height = orig.shape[0]
            width = int(orig.shape[1] * self.scale_percent / 100)
            height = int(orig.shape[0] * self.scale_percent / 100)
            dim = (width, height)

            t = self.clock()

            #  split frame into tiles so that we can have an area 
            #  for detected cards to occupy for reference
            #
            ih, iw, ic = orig.shape

            img = cv.resize(orig, dim, interpolation = cv.INTER_AREA)
            im2 = img.copy()

            #  with second plus framerates, show something on program start
            #
            if (self.frame_count == 1 or self.image_options == None or self.image_options == "V4L2"):
                self.change_pixmap_signal.emit(img)

            #try 10 by 10 grid
            rows, cols = 10,10
            tilesize = (int(ih//rows), int(iw//cols))
            self.tilesize = tilesize
            self.tileRows = 10
            self.tileCols = 10
            self.tileW = tilesize[1]
            self.tileH = tilesize[0]

        #    print(ih,iw,tilesize)
        #    print("rows %d, cols %d" % (orig.rows, orig.cols))

            #  first part is card shape detection
            #

        #    fd, hog_image = hog(img, orientations=9, pixels_per_cell=(8, 8),
        #                	cells_per_block=(2, 2), visualize=True, multichannel=True)

        #    cv.imshow('hog', hog_image)

            gray = cv.cvtColor(img, cv.COLOR_BGR2GRAY)

            # denoise before edge detection
            blur = cv.GaussianBlur(gray,(5,5),0)

            # motion detection (or lack of motion) can be detected buy comparing 
            # or subtracting the differences of the previous frame and this one
            # so we start be ensuring there is always a previous frame
            if (self.previous_frame is None):
                self.previous_frame = blur
                continue

            if (self.prev_scale != self.scale_percent):
                self.previous_frame = blur
            # motion detection
            #
            # calculate difference and update previous frame
            diff_frame = cv.absdiff(src1=self.previous_frame, src2=blur)

            same_frame = cv.bitwise_and(src1=self.previous_frame, src2=blur)

            self.previous_frame = blur

            # 4. Dilate the image a bit to make differences more seeable; more suitable for contour detection
            kernel = np.ones((5, 5))

            #diff_frame = cv.dilate(diff_frame, kernel, 1)
            diff_frame = cv.dilate(diff_frame, None, iterations=2)
            same_frame = cv.erode(same_frame, kernel, 1)

            # 5. Only take different areas that are different enough (>20 / 255)
            threshb_frame = cv.threshold(src=blur, thresh=self.threshLower, maxval=self.threshUpper, type=cv.THRESH_BINARY)[1]
            thresh_frame = cv.threshold(src=diff_frame, thresh=self.threshLower, maxval=255, type=cv.THRESH_BINARY)[1]
            same_thresh_frame = cv.threshold(src=same_frame, thresh=20, maxval=255, type=cv.THRESH_BINARY)[1]

            self.frames.insert(0,same_thresh_frame)
            if (len(self.frames) > self.framesMax):
                self.frames.pop()

            self.motion.insert(0,thresh_frame)
            if (len(self.motion) > self.motionFrames):
                self.motion.pop()

            for i in self.frames[1:]:
                same_thresh_frame = cv.add(src1=same_thresh_frame, src2=i)

            linger_frame = thresh_frame.copy()
            for i in self.motion[1:]:
                linger_frame = cv.add(src1=linger_frame, src2=i)
            
            #    cv.imshow('dilate', diff_frame)
            #    cv.imshow('motion', thresh_frame)

            #    contours, _ = cv.findContours(image=thresh_frame, mode=cv.RETR_EXTERNAL, method=cv.CHAIN_APPROX_SIMPLE)
            #    imgm = img.copy()
            #    for c in contours:
            #        if cv.contourArea(c) < 50:
            #            continue
            #        (x, y, w, h) = cv.boundingRect(c)
            #        cv.rectangle(img=imgm, pt1=(x, y), pt2=(x + w, y + h), color=(0, 255, 0), thickness=2)
            #        cv.drawContours(thresh_frame, [c], 0, (0, 255, 0), -1)

        #    cv.imshow('motion', thresh_frame)
            contours, hierarchy = cv.findContours(linger_frame, 
                cv.RETR_LIST, cv.CHAIN_APPROX_SIMPLE)

#                countours = imutils.grab_contours(contours)
            color = cv.cvtColor(linger_frame, cv.COLOR_GRAY2BGR)
            scount = 0
            for c in contours:
                if cv.contourArea(c) < 1000:
                    continue
                (x, y, w, h) = cv.boundingRect(c)
#                summons = [(60, 335),(60,230),(125,195),(265,210),(263,343)]
                summons = [(32,317),(32,215),(248,334),(251,194),(107,185)]
                for i in range(len(summons)):
                    pt = summons[i]
                    if x < pt[0] < x+w and y < pt[1] < y+h:
                        self.sawSummonsAt[i] = self.clock()

                if (self.image_options == "Motion"):
                    print ((x,y,x+w,y+h), cv.contourArea(c))
                    cv.rectangle(color, (x, y), (x + w, y + h), (0, 255, 0), 2)

            for s in range(len(self.sawSummonsAt)):
                st = self.sawSummonsAt[s]
                d = (self.clock() - st)
                if d < self.spriteMoveTime:
                    scount += 1

            self.summons = scount

            if (self.image_options == "Motion"):
                print(len(contours))
                self.change_pixmap_signal.emit(color)

            if (self.image_options == "Thresh"):
                self.change_pixmap_signal.emit(threshb_frame)

            if (self.image_options == "No Motion"):
                self.change_pixmap_signal.emit(same_thresh_frame)

        #    cv.drawContours(image=img_rgb, contours=contours, contourIdx=-1, color=(0, 255, 0), thickness=2, lineType=cv2.LINE_AA)

        #    ret, thresh1 = cv.threshold(gray, 175, 255, cv.THRESH_BINARY)
            
            #  locate X button
            #
            w, h = self.xbtn_template.shape[::-1]
            res = cv.matchTemplate(gray, self.xbtn_template, cv.TM_CCOEFF_NORMED)
            threshold = 0.8
            loc = np.where( res >= threshold)

            foundX = False
            for pt in zip(*loc[::-1]):
                cv.rectangle(im2, pt, (pt[0] + w, pt[1] + h), (0,0,255), 2)
                x = int(pt[0] + w / 2)
                y = int(pt[1] + h / 2)
                npa = np.array((x,y))
                npb = np.array((480,548)) # spell menu x button location with 9 spells
                # calculating Euclidean distance
                # using linalg.norm()
                dist = int(np.linalg.norm(npa - npb))
                if dist < 10:
                    cv.circle(im2, (x, y), 2 ,(0,0,255), 2)
                    foundX = True
                    self.spell_menu = True
            if not foundX:
                self.spell_menu = False

            hp_template = cv.imread('aethric/hp_bar_empty_alpha.png', 0)
            w, h = hp_template.shape[::-1]
            res = cv.matchTemplate(gray, hp_template, cv.TM_CCOEFF_NORMED)
            threshold = 0.8
            loc = np.where( res >= threshold)
            for pt in zip(*loc[::-1]):
                cv.rectangle(im2, pt, (pt[0] + w, pt[1] + h), (0,255,0), 2)
            # locate world bosses


            if self.mode_options == "Canny" or self.mode_options == None:
                rect = self.find_squares(blur)
            if self.mode_options == 'Thresh':
                rect = self.find_squares(blur, threshb_frame)

            words = []
            if (self.image_options in ["ReadImg"]):
                (cb, words) = self.fast_east_tess(orig)
                print(cb)
                print(words)


#            print("width %s height %s" % (self.width, self.height)) 
            #hpbar = nmpy.array([165,317,216,328])
            hptl = np.array((168,320))
            mtl = np.array((168,332)) #mana
            wtl = np.array((168,344)) #mana
            barwh = np.array((46,6))

            tl=hptl
            barimg = orig[tl[1]:tl[1]+barwh[1],tl[0]:tl[0]+barwh[0]]
            self.health_percent = self.read_percent_bar(barimg,'red') 

            tl=mtl
            barimg = orig[tl[1]:tl[1]+barwh[1],tl[0]:tl[0]+barwh[0]]
            self.mana_percent = self.read_percent_bar(barimg,'blue') 
            cv.rectangle(im2, mtl, mtl + barwh, (0, 255, 0), 2)

            tl=wtl
            barimg = orig[tl[1]:tl[1]+barwh[1],tl[0]:tl[0]+barwh[0]]
            self.ward_percent = self.read_percent_bar(barimg,'purple') 
#            health = self.read_percent_bar(hpbarimg) 
#            print("mana %.1f" % mana)
#            x, y, x2, y2 = (165,317,216,328)
#            hpbar = orig[y:y2,x:x2]
#            words = self.tess(hpbar)
#            print(words)

#            w, h = (7*4,10)
#            x, y = (254, 308)
#
#            ward = orig[y:y+h,x:x+w].copy()
#            ward = cv2.resize(ward, (280,120), interpolation=cv2.INTER_CUBIC)
##            cv.imwrite("resized.png", ward)
#
#            wt = cv2.cvtColor(ward, cv2.COLOR_BGR2HSV)
#            #white = cv2.inRange(wt, np.array([0, 0, 255]), np.array([255,255,255]))
#            white = cv2.inRange(wt, np.array([0, 0, 200]), np.array([180,20,255]))
#            wtmasked = cv2.bitwise_and(wt, wt, mask = white)
#
#            ward = cv2.cvtColor(ward, cv2.COLOR_BGR2GRAY)
#            kernel = np.ones((1, 1), np.uint8)
#            ward = cv2.dilate(ward, kernel, iterations=1)
#            ward = cv2.erode(ward, kernel, iterations=1)
# #           cv.imwrite("erode_dilate.png", ward)
#            wimg = ward.copy()
#            #ward = cv2.threshold(cv2.GaussianBlur(ward, (5, 5), 0), 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1]
#            ward = cv2.threshold(cv2.medianBlur(ward, 3), 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1]
#
#            cv.rectangle(im2, (x, y), (x+w, y+h), (255, 0, 0), 1)
#            words = self.tess(ward,"0123456789")
#            w = "".join(words)
#            if len(w):
#                self.ward_turns = int(float(w))
#                cv.imwrite("masked.png", wtmasked)
#                cv.imwrite("ward.png", ward)
#            if self.ward_turns > 0:
#                print(self.ward_turns)
#                m1 = cv2.threshold(cv2.GaussianBlur(wimg, (5, 5), 0), 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1]
#                cv.imwrite("1.png", m1)
#                m2 = cv2.threshold(cv2.bilateralFilter(wimg, 5, 75, 75), 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1]
#                cv.imwrite("2.png", m2)
#                m3 = cv2.threshold(cv2.medianBlur(wimg, 3), 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1]
#                cv.imwrite("3.png", m3)
#                m4 = cv2.adaptiveThreshold(cv2.GaussianBlur(wimg, (5, 5), 0), 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 31, 2)
#                cv.imwrite("4.png", m4)
#                m5 = cv2.adaptiveThreshold(cv2.bilateralFilter(wimg, 9, 75, 75), 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 31, 2)
#                cv.imwrite("5.png", m5)
#                m6 = cv2.adaptiveThreshold(cv2.medianBlur(wimg, 3), 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 31, 2)
#                cv.imwrite("6.png", m6)
#                #ward = cv2.threshold(cv2.bilateralFilter(ward, 5, 75, 75), 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1]
#                #cv.imwrite("thresh_filter.png", ward)
#                words = self.tess(m1,"0123456789")
#                print("^^^^ method 1")
#                words = self.tess(m2,"0123456789")
#                print("^^^^ method 2")
#                words = self.tess(m3,"0123456789")
#                print("^^^^ method 3")
#                words = self.tess(m4,"0123456789")
#                print("^^^^ method 4")
#                words = self.tess(m5,"0123456789")
#                print("^^^^ method 5")
#                words = self.tess(m6,"0123456789")
#                print("^^^^ method 6")
#                print(self.ward_turns)
#                sys.exit()

#            (cb,words) = self.fast_east_tess(boximage)
            
            if (self.image_options in ["Rects", "Arena"]):
                cardnum=0
                for cnt in rect:
                    cardnum += 1
                    box=cv.boundingRect(cnt)
                    words=[]
                    cb=[]
                    cv.drawContours(im2,[cnt],0,(0,0,255),3)
                    if  (self.image_options == "Arena"):
                        unscaled = tuple(int(n / (self.scale_percent / 100)) for n in box)
        #                print(unscaled)
                        x, y, w, h = unscaled
                        cx = x + (w / 2)
                        cy = y + (h / 2)
                        boximage=orig[y: y + h, x : x + w]

                        (cb,words) = self.fast_east_tess(boximage)

                        if len(words):
                            print(" ".join(words))
                        bt = " ".join(words)
                        if (bt in BUTTONS):
                            print(bt)
                            print(BUTTONS[bt])
#                            xt = 0
#                            yt = 0
#                            for i in range(len(cb)):
#                                cx, cy = cb[i]
#                                xt += cx
#                                yt += cy
                            #cx = (xt / len(cb)) / self.scale
                            #cy = (yt / len(cb)) / self.scale
#                            cx = (xt / len(cb))
#                            cy = (yt / len(cb))
 #                           print(cb)
#                            print("scale: %s cx: %s cy: %s" % (self.scale, cx, cy))
                            if (BUTTONS[bt] == "tap"):
                                self.actions.tap(cx,cy)
                            if (BUTTONS[bt] == "hold"):
                                self.actions.hold(cx,cy,2)

                            if (bt == "EXIT"):
                                self.actions.reset()
                            if (bt == "CONTINUE"):
                                self.actions.reset()
                            if ((bt == "HOLD SPAR") or (bt == "HOLD TO SPAR") or (bt == "HOLD BATTLE") or (bt == "HOLD TO BATTLE") or (bt == "HOLD TO BATTLE.")):
                                self.actions.reset()

                if (self.image_options in ["Arena"]):
                    self.actions.do()

            if self.show_tile_grid:
                #  display tile grid
                #
                showts = tuple(int(n * self.scale_percent / 100) for n in tilesize)
                tilecount = 0
                for col in range(cols):
                    for row in range(rows):
                        tilecount += 1
                        y0 = row * showts[0]
                        y1 = y0 + showts[0]
                        x0 = col * showts[1]
                        x1 = x0 + showts[1]

                        #show tile grids with tile number text
                        rect = cv.rectangle(im2, (x0, y0), (x1, y1), (127, 127, 127), 1)
                        cv.putText(im2, '%d' % (tilecount),
            #                       (x0 + int(showts[1] / 2), y0 + int(showts[0] / 2)),
                                   (x0 + 5, y1 - 20),
                                   cv.FONT_HERSHEY_SIMPLEX, 0.5, (127,127,127), 1)

            if (self.image_options in ["Raid"]):
                action = self.actions.action()
                if isinstance(action, dict):
                    text = "%s - %s" % (action["name"], action["action"])
                    feedback = text
                cv.putText(im2, feedback, (20, 200), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
                self.actions.do()

            if len(feedback) > 0:
                cv.putText(im2, feedback, (20, 200), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)

            if self.spell_menu:
                cv.putText(im2, "spell menu", (20, 300), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
            if self.ward_turns > 0:
                cv.putText(im2, "ward turns %s" % (self.ward_turns), (200, 300), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
            if self.health_percent > 0:
                cv.putText(im2, "health %.1f" % (self.health_percent), (220, 340), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
            if self.mana_percent > 0:
                cv.putText(im2, "mana %.1f" % (self.mana_percent), (220, 380), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
            if self.ward_percent > 0:
                cv.putText(im2, "ward %.1f" % (self.ward_percent), (220, 420), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
            if self.summons > 0:
                cv.putText(im2, "summons %s" % (self.summons), (220, 460), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)

            #  show framerate (time between processed frames)
            #
            dt = self.clock() - t
            cv.putText(im2, 'time: %.1f ms (%.1f)fps' % (dt*1000, 1/dt), (20, 20), cv.FONT_HERSHEY_SIMPLEX, 0.5, (255,255,255), 2)


#            cv.imshow(method, im2)

            #  escape key
#            if cv.waitKey(5) == 27:
#                break
#            if (self.image_options
            if (self.image_options in ["Rects", "Arena", "Raid"]):
                self.change_pixmap_signal.emit(im2)
#            print("emitting change_table with:")
#            print(self.cardsByTile)

        # shut down capture system
        cap.release()

    def clock(self):
        return cv.getTickCount() / cv.getTickFrequency()

    def get_tile(self,x,y,w,h, tilesize):
        TILE_W = tilesize[1]
        TILE_H = tilesize[0]

        x1 = int(x / TILE_W)
        x2 = (x + w) / TILE_W

        y1 = int(y / TILE_H)
        y2 = (y + h) / TILE_H

        if int(x2) == x2:
            x2 = int(x2 - 1)
        else:
            x2 = int(x2)

        if int(y2) == y2:
            y2 = int(y2 - 1)
        else:
            y2 = int(y2)

        tw = x2 - x1 + 1
        th = y2 - y1 + 1

        return x1+1, y1+1, tw, th

    def stop(self):
        """Sets run flag to False and waits for thread to finish"""
        self._run_flag = False
        self.wait()

    def set_image_options(self, option):
        if (self.debug):
            print("VideoThread: image_options: ", option)
        self.image_options = option
        if (self.image_options in ["Arena", "Raid"]):
            self.actions = Aethric(mode=self.image_options)

    def set_mode_options(self, option):
        if (self.debug):
            print("VideoThread: mode_options: ", option)
        self.mode_options = option

class WorkerSignals(QObject):
    '''
    Defines the signals available from a running worker thread.

    Supported signals are:

    finished
        No data

    error
        tuple (exctype, value, traceback.format_exc() )

    result
        object data returned from processing, anything

    progress
        int indicating % progress

    '''
    finished = pyqtSignal()
    error = pyqtSignal(tuple)
    result = pyqtSignal(object)
    progress = pyqtSignal(int)


class Worker(QRunnable):
    '''
    Worker thread

    Inherits from QRunnable to handler worker thread setup, signals and wrap-up.

    :param callback: The function callback to run on this worker thread. Supplied args and
                     kwargs will be passed through to the runner.
    :type callback: function
    :param args: Arguments to pass to the callback function
    :param kwargs: Keywords to pass to the callback function

    '''

    def __init__(self, uri, args, key):
        super(Worker, self).__init__()

        # Store constructor arguments (re-used for processing)
        self.fn = self.request
        self.uri = uri
        self.args = args
        self.key = key
        self.signals = WorkerSignals()

    def request(self):
        print("sending request to %s with %s" % (self.uri, self.args))
        response = requests.get(self.uri+self.args)
        json_response = json.loads(response.text)
        json_response["request"] = {"uri":self.uri, "args":self.args, "key":self.key}
        return json_response

    def print_output(self):
        print(self.response)

    @pyqtSlot()
    def run(self):
        '''
        Initialise the runner function with passed args, kwargs.

        # Retrieve args/kwargs here; and fire processing using them
        '''
        try:
            result = self.request()
        except:
            traceback.print_exc()
            exctype, value = sys.exc_info()[:2]
            self.signals.error.emit((exctype, value, traceback.format_exc()))
        else:
            self.signals.result.emit(result)  # Return the result of the processing
        finally:
            self.signals.finished.emit()  # Done

class RequestPool(QObject):
    on_request_result = pyqtSignal(object)
    def __init__(self):
        super().__init__()
        self.threadpool = QThreadPool()

        self.timer = QTimer()
        self.timer.setInterval(1000)
        self.timer.timeout.connect(self.recurring_timer)
        self.timer.start()
        self.uri = "https://api.scryfall.com/cards/named?fuzzy="
        self.counter = 0


    def recurring_timer(self):
        self.counter +=1

        # Execute
#        self.threadpool.start(worker)

    def result(self, response):
        (key, args, name, image, price, link) = (None, None, None, None, None,None)
        print("request pool result for %s: " % response["request"]["args"])

        args = response["request"]["args"]
        key = response["request"]["key"]

#        {'object': 'error', 'code': 'not_found', 'status': 404, 'details': 'No cards found matching “ein Eldest Redorn”'}
        try:
            print(" name  : %s" % response["name"])
            name = response["name"]
        except:
            print(response)
            return

        try:
            print(" image : %s" % response["image_uris"]["small"])
            image = response["image_uris"]["small"]
        except:
            pass

        try:
            print(" price : %s" % response["prices"]["usd"])
            price = response["prices"]["usd"]
        except:
            pass
  
        try:
            link = response["related_uris"]["gatherer"]
        except:
            pass
  
        card = {"key":key, "args":args, "name": name, "image":image, "price":price, "link": link}
        print("emit on_request_result signal ", card)
        self.on_request_result.emit(card)

        

    def make_request(self,arg,key):
        print(f"RequestPool make_request:{arg}")
        # Pass the function to execute
        uri = self.uri + arg
        worker = Worker(self.uri,arg,key) # Any other args, kwargs are passed to the run function
#        worker.signals.finished.connect(self.thread_complete)
#        worker.signals.progress.connect(self.progress_fn)
        worker.signals.result.connect(self.result)
        # Execute
        self.threadpool.start(worker)


class TransparentOverlay(QWidget):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.setAttribute(QtCore.Qt.WA_NoSystemBackground)
        self._updateParent(self.parentWidget())

    def setParent(self, parent, *args):
        prevParent = self.parentWidget()
        super().setParent(parent, *args)
        self._updateParent(parent, prevParent)

    def unsetParent(self, parent=None):
        if parent is None:
            parent = self.parentWidget()
        if parent is not None and hasattr(parent.resizeEvent, '_original'):
            parent.resizeEvent = parent.resizeEvent._original

    def _updateParent(self, parent, prevParent=None):
        if parent is not prevParent:
            self.unsetParent(prevParent)
            if parent is not None:
                original = parent.resizeEvent
                def resizeEventWrapper(event):
                    original(event)
                    self.resize(event.size())
                resizeEventWrapper._original = original
                parent.resizeEvent = resizeEventWrapper
                self.resize(parent.size())

proc = None
class ImageControl(QWidget):
    check_option_signal = pyqtSignal(str)
    check_mode_option_signal = pyqtSignal(str)

    def imageOptionClicked(self, state):
        isChecked = bool(state)
        if (isChecked):
            cb = self.checkBoxes.checkedButton()
            if (cb):
                if (self.debug):
                    print("imageOptionClicked: ",cb.text())
                self.check_option_signal.emit(cb.text())
            else:
                print("unknown button checked")

    def modeOptionClicked(self, state):
        isChecked = bool(state)
        if (isChecked):
            cb = self.modeOptions.checkedButton()
            if (cb):
                if (self.debug):
                    print("modeOptionClicked: ",cb.text())
                self.check_mode_option_signal.emit(cb.text())
            else:
                print("unknown button checked")

    def setThreshLower(self):
        self.thread.threshLower = self.t3Slider.value()
    def setThreshUpper(self):
        self.thread.threshUpper = self.t4Slider.value()
    def updateThreshLower(self, value):
        self.t3Slider.setValue(value)
    def updateThreshUpper(self, value):
        self.t4Slider.setValue(value)
    def setCannyLower(self):
        self.thread.cannyLower = self.t1Slider.value()

    def updateCannyLower(self, value):
        self.t1Slider.setValue(value)

    def setCannyUpper(self):
        self.thread.cannyUpper = self.t2Slider.value()

    def updateCannyUpper(self,value):
        self.t2Slider.setValue(value)

    def setSliderLabels(self):
        self.t1Label.setText("%d" % self.t1Slider.value())
        self.t2Label.setText("%d" % self.t2Slider.value())
        self.t3Label.setText("%d" % self.t3Slider.value())
        self.t4Label.setText("%d" % self.t4Slider.value())


    def _on_resized(self, event):
        '''
        print(ppretty(event, indent='    ', depth=2, width=30, seq_length=6,
              show_protected=True, show_private=False, show_static=True,
              show_properties=True, show_address=True))
        '''
        ow = event.oldSize().width()
        oh = event.oldSize().height()

        w = event.size().width()
        h = event.size().height()

        wd = w - ow
        hd = h - oh

        print(event.oldSize(), event.size())
        print((ow,oh), (w, h), (wd, hd))

#        self.display_width += wd
#        self.display_height += hd

#        self.image_label.resize(self.display_width, self.display_height)

    #def __init__(self,vdev=0,lower=None, upper=None, debug=False):
    def __init__(self, actions=None):
        super().__init__()
        if (not actions):
            actions = Actions()
            print("not ??")
        else:
            print(type(actions))
        self.actions = actions
#        (self.device_width,self.device_height,self.X11_width,self.X11_height) = self.actions.getResolutions()
        self.scale = 0
#self.actions.scale()

        self.display_width = 1040
        self.display_height = 720

        self.requestPool = RequestPool()

        self.resizeEvent = (lambda old_method: (lambda event: (self._on_resized(event), old_method(event))[-1]))(self.resizeEvent)
        #serial = "FAMVRW9D9HDEHEWS" #BLU Pure

        parser = optparse.OptionParser()
        parser.set_defaults(debug=False)
        parser.add_option('-d', '--debug', action='store_true', dest='debug')
        parser.add_option('--device', type="int", dest='device',
                         help="video device # to read from", default="0")
        parser.add_option('-l', '--lower', type="int", dest='lower', \
                            help="lower canny threshold for rectangle detection processing")
        parser.add_option('-u', '--upper', type="int", dest='upper', \
                            help="upper canny threshold")
        (o, args) = parser.parse_args()

        self.debug = False
        if o.debug:
            self.debug = bool(options.debug)

        self.vdev = 0
        if o.device:
            self.vdev = int(o.device)

        self.cannyLower = None
##        self.cannyLower = 50
        self.cannyLower = 40
        if o.lower:
            self.cannyLower = int(o.lower)

        self.cannyUpper = 237
        if o.upper:
            self.cannyUpper = int(o.upper)

        self.threshLower = 72 #great for high contrast mode balor
        self.threshLower = 10 #great for high contrast mode balor
        self.threshUpper = 255

        self.setWindowTitle("Image Processing Control")
        self.timeout=5
        # create the label that holds the image
        self.image_label = QLabel(self)
        self.image_label.resize(self.display_width, self.display_height)

        # create a text label
        self.textLabel = QLabel('/dev/video%d' % self.vdev)
        self.snapBtn = QPushButton('Snapshot')
        self.takeSnapshot = False
        self.snapBtn.clicked.connect(self.snapshot)

        self.t1Slider = QSlider(Qt.Horizontal)
        self.t2Slider = QSlider(Qt.Horizontal)
        self.t3Slider = QSlider(Qt.Horizontal)
        self.t4Slider = QSlider(Qt.Horizontal)
        self.t1Slider.setMinimum(0)
        self.t2Slider.setMinimum(0)
        self.t3Slider.setMinimum(0)
        self.t4Slider.setMinimum(0)
        self.t1Slider.setMaximum(255)
        self.t2Slider.setMaximum(255)
        self.t3Slider.setMaximum(255)
        self.t4Slider.setMaximum(255)
        try:
            self.t1Slider.setValue(self.cannyLower)
        except:
            self.t1Slider.setValue(0)

        try:
            self.t2Slider.setValue(self.cannyUpper)
        except:
            self.t2Slider.setValue(255)

        try:
            self.t3Slider.setValue(self.threshLower)
        except:
            self.t3Slider.setValue(0)

        try:
            self.t4Slider.setValue(self.threshUpper)
        except:
            self.t4Slider.setValue(0)


        self.t1Label = QLabel("%d" % self.t1Slider.value())
        self.t2Label = QLabel("%d" % self.t2Slider.value())
        self.t3Label = QLabel("%d" % self.t3Slider.value())
        self.t4Label = QLabel("%d" % self.t4Slider.value())
        self.t1Slider.setTickPosition(QSlider.TicksBelow)
        self.t2Slider.setTickPosition(QSlider.TicksBelow)
        self.t3Slider.setTickPosition(QSlider.TicksBelow)
        self.t4Slider.setTickPosition(QSlider.TicksBelow)
        self.t1Slider.setTickInterval(5)
        self.t2Slider.setTickInterval(5)
        self.t3Slider.setTickInterval(5)
        self.t4Slider.setTickInterval(5)
        self.t1Slider.valueChanged.connect(self.setSliderLabels)
        self.t2Slider.valueChanged.connect(self.setSliderLabels)
        self.t3Slider.valueChanged.connect(self.setSliderLabels)
        self.t4Slider.valueChanged.connect(self.setSliderLabels)
        self.t1Slider.sliderReleased.connect(self.setCannyLower)
        self.t2Slider.sliderReleased.connect(self.setCannyUpper)
        self.t3Slider.sliderReleased.connect(self.setThreshLower)
        self.t4Slider.sliderReleased.connect(self.setThreshUpper)


        self.checkBoxes = QButtonGroup()
        self.modeOptions = QButtonGroup()
        #'image options')

        hbox = QHBoxLayout()
        hbox.addWidget(self.snapBtn)
        options = [QCheckBox("V4L2"), QCheckBox("Arena"), QCheckBox("Raid"), QCheckBox("ReadImg"), QCheckBox("Rects"), QCheckBox("Thresh"),  QCheckBox("Edge C"), QCheckBox("Sq Edge"), QCheckBox("Sq Edge Contours"), QCheckBox("Motion"), QCheckBox("No Motion")]

        options[0].setChecked(True)
        for i in range(len(options)):
            hbox.addWidget(options[i])
            self.checkBoxes.addButton(options[i], i)
            options[i].stateChanged.connect(self.imageOptionClicked)

        opt2 = [QCheckBox('Thresh'), QCheckBox('Canny')]
        hboxmo = QHBoxLayout()

        opt2[1].setChecked(True)
        for i in range(len(opt2)):
            hboxmo.addWidget(opt2[i])
            self.modeOptions.addButton(opt2[i], i)
            opt2[i].stateChanged.connect(self.modeOptionClicked)

        vbox = QVBoxLayout()
        vbox.addWidget(self.image_label)
        vbox.addLayout(hbox)
        vbox.addLayout(hboxmo)
        hbt1 = QHBoxLayout()
        hbt2 = QHBoxLayout()
        hbt3 = QHBoxLayout()
        hbt4 = QHBoxLayout()
        hbt1.addWidget(self.t1Label)
        hbt1.addWidget(self.t1Slider)
        hbt2.addWidget(self.t2Label)
        hbt2.addWidget(self.t2Slider)
        hbt3.addWidget(self.t3Label)
        hbt3.addWidget(self.t3Slider)
        hbt4.addWidget(self.t4Label)
        hbt4.addWidget(self.t4Slider)
        vbox.addLayout(hbt1)
        vbox.addLayout(hbt2)
        vbox.addLayout(hbt3)
        vbox.addLayout(hbt4)
        vbox.addWidget(self.t2Slider)
        vbox.addWidget(self.textLabel)
        
        # set the vbox layout as the widgets layout
        self.setLayout(vbox)

        print("capture /dev/video%d\n" % self.vdev)

    @pyqtSlot(dict)
    def validate_text(self, card):

        #camecase, join with space
        phrase = ""
        for word in card["text"]:
            if (word.istitle()):
                phrase = "+".join([phrase, urllib.parse.quote(word)])
            else:
                phrase = "".join([phrase, urllib.parse.quote(word)])

        #even though this is likely the correct construction of the phrase,
        # there is a chance tesseract had a better OCR on one word over the other

        print("validate_text: make_request phrase %s -> %s" % ("".join(card["text"]), phrase))
        if (float(card["mconf"]) > -1):
            print(card['mconf'])
            self.requestPool.make_request(phrase, card["key"])
        else:
            print(card['mconf'])


    def run(self):
        #  will block for either timeout or time until success string outputs
        #  proc used in handler
        (proc, q) = self.v4l2sink()

#        self.isRunningOrStart() #open camera on android device


        # create the video capture thread
        self.thread = VideoThread(vdev=self.vdev,lower=self.cannyLower,upper=self.cannyUpper, lowerT=self.threshLower, upperT=self.threshUpper, debug=self.debug, actions=self.actions)
        # connect its signal to the update_image slot
        self.thread.change_pixmap_signal.connect(self.update_image)
        self.check_option_signal.connect(self.thread.set_image_options)
        self.check_mode_option_signal.connect(self.thread.set_mode_options)
        self.thread.canny_lower_signal.connect(self.updateCannyLower)
        self.thread.canny_upper_signal.connect(self.updateCannyUpper)
        self.thread.thresh_lower_signal.connect(self.updateThreshLower)
        self.thread.thresh_upper_signal.connect(self.updateThreshUpper)

        self.thread.change_text_signal.connect(self.validate_text)

        #  wait for signals to be detected so initial state is set
        #
        # start the thread
        self.thread.start()


    #  check for existing scrcpy using v42l-sink
    #  if non, start one
    #    TODO: handle errors from scrcpy
    #
    def v4l2sink(self,devN=0):

        #  check for process being run externally
        #
        try:
            fuser = subprocess.run(['fuser', "/dev/video%d" % devN], check=True, capture_output=True, text=True)
            if (len(fuser.stdout) > 0):
                m = re.match(r".*?:?\s*(?P<pid>\d+).*", fuser.stdout)
                ps = subprocess.run(['ps','-q', str(m.group('pid')), '-o', 'user=,pid=,state=,tname=,time=,command='], check=True, capture_output=True, text=True)
                if (len(ps.stdout) > 0):
                    print("v4l2 device video%d in use by the following:\n" % devN, ps.stdout)
                    return (False,False)
        except subprocess.CalledProcessError as e:
            if (e.returncode == 1 and len(e.output) == 0):
                print("v4l2 device has no current user")
            else:
                print(e.returncode)
                print(e.output)
        except BaseException as err:
            previous_frame = inspect.currentframe().f_back
            (filename, line_number, function_name, lines, index) = inspect.getframeinfo(previous_frame)
            print(f"Unexpected {err=}, {type(err)=}", line_number, lines)
            pass

        #  begin v4l2_sink with scrcpy as Popen thread with threaded output readers
        #
        print("v4l2 device currently free, starting scrcpy")
    #    cmd = "scrcpy -s %s --lock-video-orientation=3 --v4l2-sink=/dev/video0 --stay-awake --power-off-on-close --no-display --show-touches" % serial
#        cmd = "scrcpy -s %s --lock-video-orientation=3 --v4l2-sink=/dev/video0 --stay-awake --power-off-on-close --no-display --show-touches" % self.serial
        # TODO: get laptop's screensize

        wR = 0
        hR = 0
        s = self.actions.serial()
        m = self.actions.mOption()
        cmd = "scrcpy -s %s -m%s --v4l2-sink=/dev/video0 --no-display --show-touches " % (self.actions.serial(), self.actions.mOption())
        print(cmd)
        proc = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        pq = queue.Queue()
        t1 = threading.Thread(target=stdout_reader, args=(proc, pq))
        t1.start()
        t2 = threading.Thread(target=stderr_reader, args=(proc, pq))
        t2.start()

        wait = isinstance(proc, subprocess.Popen)
        waited = 0
        self.timeout = 5
        while wait and waited < self.timeout:
            try:
                line = pq.get(block=False)

                if (re.match(r"(WARN|INFO|ERROR|\[server).*", line)):
                    print('{0}'.format(line), end='')
            #INFO: v4l2 sink started to device: /dev/video0
                m = re.match(r".*?v4l2 sink started to device: (?P<device>[\/\w]+)", line)
        #        m = re.match(r".*?v4l2 sink started to device: ", line)
                if (m):
                    print("scrcpy v4l2 sink started using device %s" % m.group('device'))
                    wait = False
                #
                #  TODO what are the error strings from scrcpy or v4l2?
                #
            except queue.Empty:
                pass
            time.sleep(0.01) 
            waited += 0.01

        return (proc, pq)

    def checkCurrentFocus(self):
        cmd = "adb -s %s shell dumpsys window windows | grep -E 'mCurrentFocus|mFocusedApp|mHoldScreenWindow'"
        print(cmd)
        result = subprocess.run(cmd.split(), capture_output=True, text=True)
        return result.stdout

    #  for future reference,
    #   setting up open camera
    #  video mode, hide all gui elements
    #  set resolution to that of phone screen size
    #  enable digital video stabilization
    #  preference_auto_stabilise = true (auto level in gui)
    #    images mat be smaller resolution due to rotating and cropping
    #
    def isRunningOrStart(self,package="net.sourceforge.opencamera"):
        focus=self.checkCurrentFocus()
        m = re.match(r".*?%s.*" % package,focus)
        if (m):
            return
        else:
            cmd = "adb -s %s shell monkey -p %s -c android.intent.category.LAUNCHER 1" % (SERIAL,package)
            print(cmd)
            result = subprocess.run(cmd.split(), capture_output=True, text=True)



    def closeEvent(self, event):
        self.thread.stop()
        event.accept()

    @pyqtSlot(np.ndarray)
    def update_image(self, cv_img):
        """Updates the image_label with a new opencv image"""
        qt_img = self.convert_cv_qt(cv_img)
        self.image_label.setPixmap(qt_img)
    
    def snapshot(self):
        self.takeSnapshot = True

    def convert_cv_qt(self, cv_img):
        if (self.takeSnapshot == True):
            self.takeSnapshot = False
            cv.imwrite("snapshot.png", cv_img)
        """Convert from an opencv image to QPixmap"""
        rgb_image = cv.cvtColor(cv_img, cv2.COLOR_BGR2RGB)
        h, w, ch = rgb_image.shape
        bytes_per_line = ch * w
        convert_to_Qt_format = QtGui.QImage(rgb_image.data, w, h, bytes_per_line, QtGui.QImage.Format_RGB888)
        p = convert_to_Qt_format.scaled(self.display_width, self.display_height, Qt.KeepAspectRatio)
        return QPixmap.fromImage(p)
    
if __name__=="__main__":
    signal.signal(signal.SIGINT, handler)
    app = QApplication(sys.argv)
    main = ImageControl(actions=Aethric())
    main.run()
    cb = main.checkBoxes.checkedButton()
    if (cb):
        print("imageOptionClicked: ",cb.text())
        main.check_option_signal.emit(cb.text())
    main.show()
    #  cleanup after Popen
    frame = inspect.currentframe()
    handler(signal.SIGINT, frame)

