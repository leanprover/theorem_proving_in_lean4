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
        echo "$CHAPTER -> ${TUTORIAL_ORG_FILE}"
        cp -- ${CHAPTER} ${TUTORIAL_ORG_FILE}
    else
        START_LINE=`grep -n '^\* ' ${CHAPTER} | cut -d ':' -f 1`
        echo "$CHAPTER : +${START_LINE} -> ${TUTORIAL_ORG_FILE}"
        tail -n +${START_LINE} -- ${CHAPTER} >> ${TUTORIAL_ORG_FILE}
    fi
done

# Replace inter-file links to inner-file links
#
# Example:
#
#     In Section [[file:05_Interacting_with_Lean.org::Notation_Overloads_and_Coercions][Notations, Overloads, and Coercions]], we discussed coercions
#
# =>
#
#     In Section [[Notation_Overloads_and_Coercions][Notations, Overloads, and Coercions]], we discussed coercions
sed -e "s/file:[0-9][0-9]_[^:]*.org:://g" ${TUTORIAL_ORG_FILE} > ${TUTORIAL_ORG_FILE}.tmp
mv -v ${TUTORIAL_ORG_FILE}.tmp  ${TUTORIAL_ORG_FILE}
