#!/usr/bin/env bash
#
# Copyright (c) 2014 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Author: Soonho Kong
#
# Collect 01_xxx.org, 02_xxx.org, ... files and merge them into tutorial.org file
#
TUTORIAL_ORG_FILE=tutorial.org

rm -f ${TUTORIAL_ORG_FILE}
for CHAPTER in [0-9][0-9]*.org
do
    if [ ! -f ${TUTORIAL_ORG_FILE} ] ; then
        cp -v $CHAPTER tutorial.org
    else
        START_LINE=`grep -n '^\* ' ${CHAPTER} | cut -d ':' -f 1`
        tail -n +${START_LINE} $CHAPTER >> ${TUTORIAL_ORG_FILE}
    fi
done
