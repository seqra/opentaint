package org.opentaint.jvm.dataflow.approximations.spring;

import org.opentaint.ir.approximation.annotation.ApproximateByName;

@ApproximateByName("org.springframework.util.StringUtils")
public class StringUtils {

    public static String arrayToCommaDelimitedString(Object[] arr) {
        if (arr == null) return "";
        StringBuilder sb = new StringBuilder();
        for (Object elem : arr) {
            sb.append(elem.toString());
        }
        return sb.toString();
    }
}
