package info.kgeorgiy.ja.yaroshevskij.student;

import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import info.kgeorgiy.java.advanced.student.*;

public class StudentDB implements GroupQuery {

    private final Comparator<Group> groupSizeComparator = Comparator.comparing(group -> group.getStudents().size());
    private final Comparator<Student> studentComparator = Comparator.naturalOrder();
    private final Comparator<Student> studentNameComparator =
            Comparator.comparing(Student::getLastName).reversed()
                    .thenComparing(Comparator.comparing(Student::getFirstName).reversed())
                    .thenComparing(studentComparator);

    private String getStudentFullName(Student student) {
        return student.getFirstName() + " " + student.getLastName();
    }

    private <T> Predicate<Student> studentWithField(Function<Student, T> keyExtractor, T key) {
        return student -> keyExtractor.apply(student).equals(key);
    }

    private Predicate<Student> studentWithGroup(GroupName groupName) {
        return studentWithField(Student::getGroup, groupName);
    }

    private Predicate<Student> studentWithFirstName(String firstName) {
        return studentWithField(Student::getFirstName, firstName);
    }

    private Predicate<Student> studentWithLastName(String lastName) {
        return studentWithField(Student::getLastName, lastName);
    }

    private <T, C extends Collection<T>> C studentsToCollectionWith(Function<Student, T> function,
                                                                    Collection<Student> students,
                                                                    Collector<T, ?, C> collector) {
        return students.stream()
                .map(function)
                .collect(collector);
    }

    private <T> List<T> studentsToListWith(Function<Student, T> function, Collection<Student> students) {
        return studentsToCollectionWith(function, students, Collectors.toList());
    }

    private List<Student> toSortedList(Stream<Student> stream, Comparator<Student> comparator) {
        return stream.sorted(comparator).collect(Collectors.toList());
    }

    private List<Student> toSortedList(Stream<Student> stream) {
        return toSortedList(stream, studentNameComparator);
    }

    @Override
    public Map<String, String> findStudentNamesByGroup(Collection<Student> students, GroupName groupName) {
        return students.stream()
                .filter(studentWithGroup(groupName))
                .collect(Collectors.groupingBy(
                        Student::getLastName,
                        Collectors.collectingAndThen(
                                Collectors.minBy(Comparator.comparing(Student::getFirstName)),
                                opt -> opt.map(Student::getFirstName).orElse(null))));
    }

    @Override
    public List<Student> findStudentsByFirstName(Collection<Student> students, String firstName) {
        return toSortedList(students.stream()
                .filter(studentWithFirstName(firstName)));
    }

    @Override
    public List<Student> findStudentsByGroup(Collection<Student> students, GroupName groupName) {
        return toSortedList(students.stream()
                .filter(studentWithGroup(groupName)));
    }

    @Override
    public List<Student> findStudentsByLastName(Collection<Student> students, String lastName) {
        return toSortedList(students.stream()
                .filter(studentWithLastName(lastName)));
    }

    @Override
    public Set<String> getDistinctFirstNames(List<Student> students) {
        return studentsToCollectionWith(Student::getFirstName, students, Collectors.toCollection(TreeSet::new));
    }

    @Override
    public List<String> getFirstNames(List<Student> students) {
        return studentsToListWith(Student::getFirstName, students);
    }

    @Override
    public List<String> getFullNames(List<Student> students) {
        return studentsToListWith(this::getStudentFullName, students);
    }

    @Override
    public List<GroupName> getGroups(List<Student> students) {
        return studentsToListWith(Student::getGroup, students);
    }

    @Override
    public List<String> getLastNames(List<Student> students) {
        return studentsToListWith(Student::getLastName, students);
    }

    @Override
    public String getMaxStudentFirstName(List<Student> students) {
        return students.stream()
                .max(studentComparator)
                .map(Student::getFirstName)
                .orElse("");
    }

    @Override
    public List<Student> sortStudentsById(Collection<Student> students) {
        return toSortedList(students.stream(), studentComparator);
    }

    @Override
    public List<Student> sortStudentsByName(Collection<Student> students) {
        return toSortedList(students.stream());
    }

    private <C extends Collection<Student>> Stream<Group> groupsStream(Collection<Student> students,
                                                                       Comparator<Student> comparator,
                                                                       Collector<Student, ?, C> collector,
                                                                       Function<C, List<Student>> toList) {
        return students.stream()
                .sorted(comparator)
                .collect(Collectors.groupingBy(Student::getGroup, collector))
                .entrySet().stream()
                .map(entry -> new Group(entry.getKey(), toList.apply(entry.getValue())));
    }

    private Stream<Group> groupsStream(Collection<Student> students, Comparator<Student> comparator) {
        return groupsStream(students, comparator, Collectors.toList(), Function.identity());
    }

    private List<Group> getSortedGroups(Collection<Student> students, Comparator<Student> comparator) {
        return groupsStream(students, comparator)
                .sorted(Comparator.comparing(Group::getName))
                .collect(Collectors.toList());
    }

    private GroupName maxGroupBy(Stream<Group> stream, Comparator<Group> comparator) {
        return stream.max(comparator).map(Group::getName).orElse(null);
    }

    @Override
    public List<Group> getGroupsByName(Collection<Student> students) {
        return getSortedGroups(students, studentNameComparator);
    }

    @Override
    public List<Group> getGroupsById(Collection<Student> students) {
        return getSortedGroups(students, studentComparator);
    }

    //todo copy-paste
    @Override
    public GroupName getLargestGroup(Collection<Student> students) {
        return maxGroupBy(groupsStream(students, studentNameComparator),
                groupSizeComparator.thenComparing(Group::getName));
    }

    @Override
    public GroupName getLargestGroupFirstName(Collection<Student> students) {
        return maxGroupBy(
                groupsStream(students,
                        studentComparator,
                        Collectors.toCollection(
                                () -> new TreeSet<>(Comparator.comparing(Student::getFirstName))),
                        ArrayList::new),
                groupSizeComparator.reversed().thenComparing(Group::getName).reversed());
    }
}
