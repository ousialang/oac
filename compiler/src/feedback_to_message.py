#!/usr/bin/env python
# -*- coding: utf-8 -*-

import flatbuffers

def feedback_to_message():
    monster = MyGame.Sample.Monster.Monster.GetRootAsMonster(buf, 0)
    formula_length = len(monster.Formula())

