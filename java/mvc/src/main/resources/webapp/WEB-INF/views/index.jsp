<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8"%>
<%@ taglib prefix="form" uri="http://www.springframework.org/tags/form"%>
<%@ taglib prefix="c" uri="http://java.sun.com/jstl/core_rt" %>

<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<head>
    <title>Add question</title>
</head>
<body>

<h3>Select products</h3>
<form:form modelAttribute="filter" method="GET" action="/filter-products">
    <form:select path="filter">
        <form:option value="all">all</form:option>
        <form:option value="max">max</form:option>
        <form:option value="min">min</form:option>
    </form:select>
    <input type="submit" value="filter">
</form:form>

<table>
    <c:forEach var="product" items="${products}">
    <tr>
        <td>${product.getId()}</td>
        <td>${product.getName()}</td>
        <td>${product.getPrice()}</td>
    </tr>
    </c:forEach>
</table>

<h3>Add new products</h3>
<form:form modelAttribute="product" method="POST" action="/add-product">
    <table>
        <tr>
            <td><form:label path="name">Name:</form:label></td>
            <td><form:input path="name"/></td>
        </tr>
        <tr>
            <td><form:label path="price">Price:</form:label></td>
            <td><form:input path="price"/></td>
        </tr>
    </table>

    <input type="submit" value="add">
</form:form>
</body>
</html>
